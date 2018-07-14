
;; This file contains functions and stobjs used by multiple
;; files in our SAT-based conversion algorithm.

(in-package "SAT")

(program)
(set-state-ok t)

;; For now at least, I'm going to have a maximum number
;; of intermediate variables.  I could use resizable array's,
;; for now, I'd like to avoid the hassle.

;; The following is a bad programming practice---a bound
;; on the number of variables.  I need to fix it, because
;; it's starting to hurt me.
; Changed by Matt K. to avoid make-array$ error caused in Lispworks 4.4.6,
; because array-total-size-limit = 1048448.  Erik Reeber says (email
; communicate, 7/31/08) that he had "upped the number of variables" because one
; of his proofs needed the increase, but that this proof is no longer run.
;(defconst *max-vars* 3000000)
(defconst *max-vars* 1000000)

(defconst acl2::*sat-max-entry-id* *max-vars*)

(defconst *init-array-size* 1000)

;; The maximum number of final variables.  I think 10 million
;; should be plenty.

(defmacro sat-stobj ()
  `(defstobj $sat

     ;; Whether another traversal is needed in order to convert the
     ;; expression to SAT
     (need-more-traversals :type t :initially nil)

     ;; The intermediate variables, used to denote list expressions of
     ;; the inputs---e.g. (cadddr i)
     (num-i-vars :type (integer 0 ,*max-vars*) :initially 0)

     (car-var :type (array (integer 0 ,*max-vars*) (0))
              :initially 0 :resizable t)
     (cdr-var :type (array (integer 0 ,*max-vars*) (0))
              :initially 0 :resizable t)

     ;; Parrent of the list expression---e.g.
     ;; 5=(car 6) => (cons-var 5)=6
     (cons-var :type (array (integer 0 ,*max-vars*) (0))
               :initially 0 :resizable t)

     (stack-number :type (integer 0 ,*max-vars*) :initially 0)
     (traversal-number :type (integer 0 ,*max-vars*) :initially 0)

     (stack-num :type (array (integer 0 ,*max-vars*) (0))
                :initially 0 :resizable t)

     (traversal-num :type (array (integer 0 ,*max-vars*) (0))
                    :initially 0 :resizable t)

     ;; Whether an i-variable is relevant to its next traversal
     ;; (1=true, 0=false)
     (relevant-ivar :type (array (integer 0 1) (0))
                    :initially 0 :resizable t)

     ;; A list of things "todo" when traversing a given variable.
     ;; This generally amounts to setting it equal to its definition.
     ;; The todo-struct is of the form:
     ;; (<todo-list> . <i-todo-list>)
     ;; Where todo-list is a list of todo-entries involving
     ;; ACL2 expressions and i-todo-list is a list of todo-entries
     ;; involving i-expressions (see terminology section in
     ;; conert-to-cnf.lisp).
     (todo-struct :type (array t (0))
                  :initially nil :resizable t)

     ;; The final variables associated with a given intermediate variable
     (num-f-vars :type (integer 0 ,*max-vars*) :initially 0)

     ;; Whether a final variable is relevant to the next traversal
     ;; (1=true, 0=false)
     (relevant-fvar :type (array (integer 0 1) (0))
                    :initially 0 :resizable t)

     (eq-nil-var :type (array (integer 0 ,*max-vars*) (0))
                 :initially 0 :resizable t)
     (consp-var :type (array (integer 0 ,*max-vars*) (0))
                :initially 0 :resizable t)

     ;; A structure mapping (eq x a0) to f-vars, where a0 is an atomic
     ;; constant.
     (eq-const-struct-var :type (array t (0)) :initially nil :resizable t)

     ;; An alist mapping (eq x y) to f-vars, where both x and y are
     ;; i-vars.
     (eq-alist-var :type (array t (0)) :initially nil :resizable t)

     ;; The counter example values
     (ce-val :type (array (integer 0 1) (0))
             :initially 0 :resizable t)

     ;; Associates an i-var with its quoted constant counter-example
     ;; value or nil if no such value is present.
     (ce-i-var-val :type (array t (0)) :initially 'sat::unknown :resizable t)

     (unused-num :type t :initially 0)

     ;; A stack representing variables that need to be
     ;; traversed.  By which we mean that the main expression
     ;; looks like:
     ;; (let ((var0 ...)
     ;;       (var1 ...)
     ;;       ...
     ;;       (varN ...))
     ;;    ...)
     ;; And this stack represents variables in the let expression
     ;; that haven't been set equal to their definitions.  The
     ;; traversal is in bottom-up order to support a cone-of-influence
     ;; reduction.
     (var-stack :type t :initially nil)

     (top-var-stack :type t :initially nil)

     ;; During variable traversal, this is a stack of variables that have
     ;; been traversed.
     ;;
     ;; Afterward, this is a list of all top-level variables in the problem,
     ;; in the reverse oder of their traversal.
     (completed-var-list :type t :initially nil)

     (top-completed-var-list :type t :initially nil)

     ;; The mapping of variables in the input to
     ;; intermediate variables.
     (input-alist :type t :initially nil)

     (num-f-clauses :type integer :initially 0)

     (num-f-clauses-pre-explore :type integer :initially 0)

     (sat-input-channel :type t :initially nil)

     (top-var-eql :type (array (integer 0 1) (0))
              :initially 0 :resizable t)

     (pos-var :type (array (integer 0 1) (0))
              :initially 0 :resizable t)
     (neg-var :type (array (integer 0 1) (0))
              :initially 0 :resizable t)

     (cet-entry :type (array t (0)) :resizable t)
     (num-cete :type integer :initially 0)

     (un-fn-list :type t :initially nil)

     (problem-stack-depth :type (integer 0 10) :initially 0)

     (explore-var-list :type t :initially nil)
     (curr-ord-entry-list :type t :initially nil)
     (saved-ord-entry-list :type t :initially nil)
     (exploration-val-list :type t :initially nil)

     (un-fn-world :type t :initially nil)

     (props-world :type t :initially nil)

     (NLA-table :type t :initially nil)

     ;; This value is left for others tools to play with.
     (external-value :type t :initially nil)

     (verbosity :type (integer 0 4) :initially 1)
     ))

(sat-stobj)

;; Variables can't be zero, so we use that whenever
;; we use 0 to say that there is no such variable.
(defun valid-varp (var)
  (and (integerp var)
       (< 0 var)))

(defun zero-sat-input-channel ($sat state)
  (declare (xargs :stobjs $sat))
  (let ((channel (sat-input-channel $sat)))
    (cond
     (channel
      (let* ((state (close-output-channel (sat-input-channel $sat)
                                          state))
             ($sat (update-sat-input-channel nil $sat)))
        (mv $sat state)))
     (t
      (mv $sat state)))))

;; Before begining conversion, we generally zero-out
;; the stobj to assure that no outside data gets in.
(defun zero-sat-stobj ($sat state)
  (declare (xargs :stobjs $sat))
  (let* (($sat (update-need-more-traversals nil $sat))
         ($sat (update-num-i-vars 0 $sat))
         ($sat (resize-car-var 0 $sat))
         ($sat (resize-cdr-var 0 $sat))
         ($sat (resize-cons-var 0 $sat))
         ($sat (update-stack-number 0 $sat))
         ($sat (update-traversal-number 0 $sat))
         ($sat (resize-stack-num 0 $sat))
         ($sat (resize-traversal-num 0 $sat))
         ($sat (resize-relevant-ivar 0 $sat))
         ($sat (resize-todo-struct 0 $sat))
         ($sat (update-num-f-vars 0 $sat))
         ($sat (resize-relevant-fvar 0 $sat))
         ($sat (resize-eq-nil-var 0 $sat))
         ($sat (resize-consp-var 0 $sat))
         ($sat (resize-eq-const-struct-var 0 $sat))
         ($sat (resize-eq-alist-var 0 $sat))
         ($sat (resize-ce-val 0 $sat))
         ($sat (resize-ce-i-var-val 0 $sat))
         ($sat (update-unused-num 0 $sat))
         ($sat (update-var-stack nil $sat))
         ($sat (update-top-var-stack nil $sat))
         ($sat (update-completed-var-list nil $sat))
         ($sat (update-top-completed-var-list nil $sat))
         ($sat (update-input-alist nil $sat))
         ($sat (update-num-f-clauses 0 $sat))
         ($sat (update-num-f-clauses-pre-explore 0 $sat))
         ($sat (resize-top-var-eql 0 $sat))
         ($sat (resize-pos-var 0 $sat))
         ($sat (resize-neg-var 0 $sat))

         ;;($sat (resize-cet-entry 0 $sat))
         ($sat (update-num-cete 0 $sat))
         ($sat (update-un-fn-list nil $sat))

         ($sat (update-problem-stack-depth 0 $sat))

         ($sat (update-explore-var-list nil $sat))
         ($sat (update-curr-ord-entry-list nil $sat))
         ($sat (update-saved-ord-entry-list nil $sat))
         ($sat (update-exploration-val-list nil $sat))

         ($sat (update-un-fn-world nil $sat))
         ;; I don't zero-out the props-world or
         ;; NLA table since they store info that
         ;; shouldn't change from one problem to the
         ;; next.
         )
    (zero-sat-input-channel $sat state)))

(defun zero-ce-vals ($sat)
  (declare (xargs :stobjs $sat))
  (let* (($sat (resize-ce-val 0 $sat))
         ($sat (resize-ce-i-var-val 0 $sat))
         ($sat (update-unused-num 0 $sat)))
    $sat))

(defun zero-sat-stobj! ($sat state)
  (declare (xargs :stobjs $sat))
  (mv-let
   ($sat state)
   (zero-sat-stobj $sat state)
   (let* (($sat (zero-ce-vals $sat))
          ($sat (update-props-world nil $sat))
          ($sat (update-NLA-table nil $sat)))
     (mv $sat state))))

;; Before begining a new :sat call, I allocate space for all
;; the arrays
(defun construct-sat-stobj ($sat)
  (declare (xargs :stobjs $sat))
  (let* (($sat (resize-cet-entry *init-array-size* $sat))
         ($sat (resize-car-var (1+ *max-vars*) $sat))
         ($sat (resize-cdr-var (1+ *max-vars*) $sat))
         ($sat (resize-cons-var (1+ *max-vars*) $sat))
         ($sat (resize-stack-num (1+ *max-vars*) $sat))
         ($sat (resize-traversal-num (1+ *max-vars*) $sat))
         ($sat (resize-eq-const-struct-var (1+ *max-vars*) $sat))
         ($sat (resize-eq-alist-var (1+ *max-vars*) $sat))
         ($sat (resize-relevant-ivar (1+ *max-vars*) $sat))
         ($sat (resize-todo-struct (1+ *max-vars*) $sat))
         ($sat (resize-relevant-fvar (1+ *max-vars*) $sat))
         ($sat (resize-eq-nil-var (1+ *max-vars*) $sat))
         ($sat (resize-consp-var (1+ *max-vars*) $sat))
         ($sat (resize-top-var-eql (1+ *max-vars*) $sat))
         ($sat (resize-pos-var (1+ *max-vars*) $sat))
         ($sat (resize-neg-var (1+ *max-vars*) $sat)))
    $sat))

(defun top-varp (var $sat)
  (declare (xargs :stobjs $sat))
  (equal 1 (top-var-eqli var $sat)))

(defun construct-ce-vals ($sat)
  (declare (xargs :stobjs $sat))
  (let* (($sat (resize-ce-val *max-vars* $sat))
         ($sat (resize-ce-i-var-val *max-vars* $sat)))
    $sat))

;; Get the formals of a function.
(defun fn-formals (fn state)
  (cond
   ((consp fn) ;; (lambda formals body)
    (cadr fn))
   (t
    (let ((formals (getprop fn
                            'acl2::formals
                            'not-found
                            'acl2::current-acl2-world
                            (w state))))
      (if (not (equal formals 'not-found))
          formals
        (er hard
            'fn-formals
            "Unable to get formals of function ~x0 ~%"
            fn))))))

;; Get the body of a function or return
;; nil if the body does not exist.
(defun fn-body! (fn state)
  (cond
   ((consp fn) ;; (lambda formals body)
    (caddr fn))
   (t
    (getprop
     fn
     'acl2::unnormalized-body
     nil
     'acl2::current-acl2-world
     (w state)))))

;; Get the body of a function or error
;; if the body does not exist.
(defun fn-body (fn state)
  (let ((body (fn-body! fn state)))
    (if body body
      (er hard
          'fn-body
          "Unable to get body of function ~x0, returned ~x1 ~%"
          fn
          body))))

;; Get the justifying measure of a function.
(defun fn-justification (fn state)
  (getprop fn
           'acl2::justification
           #!acl2(make justification
                       :subset ()
                       :mp 'o-p
                       :rel 'o-<
                       :measure '(quote 0)
                       :ruler-extenders *basic-ruler-extenders*)
           'acl2::current-acl2-world
           (w state)))

(defun concat-macro (lst)
  (if (consp lst)
      (if (consp (cdr lst))
	  (cons 'concatenate
		(cons ''string (cons (car lst)
				     (cons (concat-macro (cdr lst))
					   'nil))))
	(car lst))
    nil))

(defmacro concat (&rest args)
  (concat-macro args))

(defun get-unused-number ($sat)
  (declare (xargs :stobjs $sat))
  (let* ((n (unused-num $sat))
         ($sat (update-unused-num (1+ n) $sat)))
    (mv n $sat)))

;; Convert a non-negative number to a string

(defun num-to-str (n)
  (coerce (explode-nonnegative-integer n 10 nil) 'string))

(defun add-input-alist-entry (input-var i0 $sat)
  (declare (xargs :stobjs $sat))
  (update-input-alist (cons (cons input-var i0)
                            (input-alist $sat))
                      $sat))

;; Sometimes I use the numbers 1 and 0 to represent the
;; Booleans 't and 'nil:

(defun constp (x)
  (if (atom x) nil (quotep x)))

(defun ++i-var ($sat)
  (declare (xargs :stobjs $sat))
  (let* ((i-var (num-i-vars $sat))
         (i-var (1+ i-var))
         ($sat (update-num-i-vars i-var $sat)))
    (mv i-var $sat)))

(defun ++f-var ($sat)
  (declare (xargs :stobjs $sat))
  (let* ((f-var (num-f-vars $sat))
         (f-var (1+ f-var))
         ($sat (update-num-f-vars f-var $sat))
         ($sat (update-relevant-fvari f-var 1 $sat)))
    (mv f-var $sat)))

;; A variable is irrelevant if we haven't created
;; variables for its car, cdr, bfix, or consp.
(defun irrelevant-ivarp (i-var $sat)
  (declare (xargs :stobjs $sat))
  (equal 0 (relevant-ivari i-var $sat)))

(defun relevant-f-varp (f-var $sat)
  (declare (xargs :stobjs $sat))
  (equal 1 (relevant-fvari f-var $sat)))

;; If a variable is relevant, then all its
;; parents are also relevant---e.g.
;; if 6=(car 5) is relevant, then so is 5.
(defun mark-ivar-relevant (var $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal (relevant-ivari var $sat) 1)
    $sat)
   (t
    (let* (($sat (update-relevant-ivari var 1 $sat))
           (parent (cons-vari var $sat)))
      (cond
       ((not (valid-varp parent))
        $sat)
       (t
        (mark-ivar-relevant parent $sat)))))))

(defun mark-fvar-irrelevant (f-var $sat)
  (declare (xargs :stobjs $sat))
  (if (valid-varp f-var)
      (update-relevant-fvari f-var 0 $sat)
    $sat))

;; We can just mark the first entry irrelevant, since
;; if an alists first entry is irrelevant, the whole
;; thing is considered irrelevant.
(defun mark-alist-irrelevant (alist $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp alist)
    $sat)
   (t
    (update-relevant-fvari (cdr (car alist)) 0 $sat))))

;; Candidate for tail-recursive optimization!!!
(defun mark-ivar-irrelevant (var $sat)
  (declare (xargs :stobjs $sat))
  (let* (($sat (update-relevant-ivari var 0 $sat))
         ($sat (mark-fvar-irrelevant (eq-nil-vari var $sat) $sat))
         ($sat (mark-fvar-irrelevant (consp-vari var $sat) $sat))
         (eq-const-struct (eq-const-struct-vari var $sat))
         ($sat (mark-fvar-irrelevant (car eq-const-struct) $sat))
         ($sat (mark-alist-irrelevant (eq-alist-vari var $sat) $sat))
         ($sat (mark-alist-irrelevant (cdr eq-const-struct) $sat))
         (car-var (car-vari var $sat))
         (cdr-var (cdr-vari var $sat))
         ($sat (if (and (valid-varp car-var)
                        (equal (relevant-ivari car-var $sat) 1))
                   (mark-ivar-irrelevant car-var $sat)
                 $sat)))
    (if (and (valid-varp cdr-var)
             (equal (relevant-ivari cdr-var $sat) 1))
        (mark-ivar-irrelevant cdr-var $sat)
      $sat)))

;; The next five functions are deal with the internal structure
;; of how variables are associated with (eq x a) where a is an
;; atomic constant.  I try to keep exactly how this structe is
;; maintained abstracted from the rest of the function.  For
;; efficienty though, an array is used to represent the common
;; (eq x nil) variable.   Meanwhile the less common (eq x t) is
;; kept as the first entry in eq-const-struct.  The rest of the
;; struct is an alist of the othe, less common, atomic constants
;; to which a variable x may be equal.
;;    eq-nil-vari is also constidered an abstract accessor function, but
;; is defined directly through the $sat stobj.

(defun eq-t-vari (var $sat)
  (declare (xargs :stobjs $sat))
  (car (eq-const-struct-vari var $sat)))

(defun valid-Booleanp (var $sat)
  (declare (xargs :stobjs $sat))
  (or (valid-varp (eq-nil-vari var $sat))
      (valid-varp (eq-t-vari var $sat))))

;; Note: Whenever we return an alist, all entries
;; after the first irrelevant entry is irrelevant.
(defun insert-after-relevant-vars (key val alist front-ans $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp alist)
    (revappend front-ans (list (cons key val))))
   ((relevant-f-varp (cdr (car alist)) $sat)
    (insert-after-relevant-vars key
                                val
                                (cdr alist)
                                (cons (car alist) front-ans)
                                $sat))
   (t
    (revappend front-ans (cons (cons key val) alist)))))

(defun add-alist-entry (key f-var alist $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((not (valid-varp f-var))
    alist)
   ((relevant-f-varp f-var $sat)
    (cons (cons key f-var) alist))
   (t
    (insert-after-relevant-vars key f-var alist nil $sat))))

(defun non-nil-atoms-alist-vari (var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((eq-const-struct (eq-const-struct-vari var $sat))
         (eq-t (car eq-const-struct))
         (eq-const-alist (cdr eq-const-struct)))
    (add-alist-entry t eq-t eq-const-alist $sat)))

(defun atoms-alist-vari (var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((eq-nil (eq-nil-vari var $sat))
         (non-nil-atoms (non-nil-atoms-alist-vari var $sat)))
    (add-alist-entry nil eq-nil non-nil-atoms $sat)))

(defun pop-eq-atom-entry (var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((eq-nil (eq-nil-vari var $sat))
         (eq-const-struct (eq-const-struct-vari var $sat))
         (eq-t (car eq-const-struct))
         (eq-const-alist (cdr eq-const-struct)))
    (cond
     ((valid-varp eq-nil)
      (let (($sat (update-eq-nil-vari var 0 $sat)))
        (mv nil eq-nil $sat)))
     ((valid-varp eq-t)
      (let* ((eq-const-struct (cons 0 eq-const-alist))
             ($sat (update-eq-const-struct-vari var eq-const-struct $sat)))
        (mv t eq-t $sat)))
     ((endp eq-const-alist)
      (mv 0 0 $sat))
     (t
      (let* ((a (caar eq-const-alist))
             (eq-var-a (cdar eq-const-alist))
             (eq-const-struct (cons 0 (cdr eq-const-alist)))
             ($sat (update-eq-const-struct-vari var eq-const-struct $sat)))
        (mv a eq-var-a $sat))))))

(defun pop-eq-alist-entry (var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((eq-alist (eq-alist-vari var $sat)))
    (cond
     ((endp eq-alist)
      (mv 0 0 $sat))
     (t
      (let* ((y (caar eq-alist))
             (eq-var-y (cdar eq-alist))
             ($sat (update-eq-alist-vari var (cdr eq-alist) $sat)))
        (mv y eq-var-y $sat))))))

(defun unravel-atoms-alist (atoms-alist)
  (cond
   ((endp atoms-alist)
    (mv 0 0 nil))
   ((eq nil (caar atoms-alist))
    (mv-let
     (eq-nil eq-t non-nil-atoms)
     (unravel-atoms-alist (cdr atoms-alist))
     (declare (ignore eq-nil))
     (mv (cdar atoms-alist) eq-t non-nil-atoms)))
   ((eq t (caar atoms-alist))
    (mv-let
     (eq-nil eq-t non-nil-atoms)
     (unravel-atoms-alist (cdr atoms-alist))
     (declare (ignore eq-t))
     (mv eq-nil (cdar atoms-alist) non-nil-atoms)))
   (t
    (mv-let
     (eq-nil eq-t non-nil-atoms)
     (unravel-atoms-alist (cdr atoms-alist))
     (mv eq-nil eq-t (cons (car atoms-alist) non-nil-atoms))))))

(defun update-atoms-alist-vari (var atoms-alist $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (eq-nil eq-t non-nil-atoms)
   (unravel-atoms-alist atoms-alist)
   (let* (($sat (update-eq-nil-vari var eq-nil $sat))
          (eq-const-struct (cons eq-t non-nil-atoms)))
     (update-eq-const-struct-vari var eq-const-struct $sat))))


;; Get the f-var associated with (eq var nil),
;; creating one if it doesn't already exist.
(defun create-eq-nil-var (var $sat)
  (declare (xargs :stobjs $sat))
  (let ((eq-nil-var (eq-nil-vari var $sat)))
    (if (valid-varp eq-nil-var)
        (mv eq-nil-var $sat)
      (mv-let
       (eq-nil-var $sat)
       (++f-var $sat)
       (let* (($sat (update-eq-nil-vari var eq-nil-var $sat))
              ($sat (mark-ivar-relevant var $sat)))
         (mv eq-nil-var $sat))))))

;; Get the f-var associated with (eq var a),
;; returning an invalid variable if one doesn't exist.
(defun lookup-atom-var (var a $sat)
  (declare (xargs :stobjs $sat))
(cond
   ((eq a nil)
    (eq-nil-vari var $sat))
   ((eq a t)
    (eq-t-vari var $sat))
   (t
    (let*  ((eq-const-struct (eq-const-struct-vari var $sat))
            (eq-const-alist (cdr eq-const-struct))
            (eq-const-entry (assoc-equal a eq-const-alist)))
      (if eq-const-entry
          (cdr eq-const-entry)
        0)))))

;; Get the f-var associated with (eq var a),
;; creating one if it doesn't already exist.
;; Here a is some atomic constant.
(defun create-atom-var (var a $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((eq a nil)
    (create-eq-nil-var var $sat))
   ((eq a t)
    (let ((eq-const-struct (eq-const-struct-vari var $sat)))
    (if (valid-varp (car eq-const-struct))
        (mv (car eq-const-struct) $sat)
      (mv-let
       (eq-t-var $sat)
       (++f-var $sat)
       (let* (($sat (update-eq-const-struct-vari
                     var
                     (cons eq-t-var (cdr eq-const-struct))
                     $sat))
              ($sat (mark-ivar-relevant var $sat)))
         (mv eq-t-var $sat))))))
   (t
    (let*  ((eq-const-struct (eq-const-struct-vari var $sat))
            (eq-const-alist (cdr eq-const-struct))
            (eq-const-entry (assoc-equal a eq-const-alist)))
      (if eq-const-entry
          (mv (cdr eq-const-entry) $sat)
        (mv-let
         (eq-a-var $sat)
         (++f-var $sat)
         (let* ((eq-const-alist (cons (cons a eq-a-var) eq-const-alist))
                ($sat (update-eq-const-struct-vari var
                                                   (cons (car eq-const-struct)
                                                         eq-const-alist)
                                                   $sat))
                ($sat (mark-ivar-relevant var $sat)))
           (mv eq-a-var $sat))))))))

;; Get the f-var associated with (consp var),
;; creating one if it doesn't already exist.
(defun create-consp-var (var $sat)
  (declare (xargs :stobjs $sat))
  (let ((consp-var (consp-vari var $sat)))
    (if (valid-varp consp-var)
        (mv consp-var $sat)
      (mv-let
       (consp-var $sat)
       (++f-var $sat)
       (let* (($sat (update-consp-vari var consp-var $sat))
              ($sat (mark-ivar-relevant var $sat)))
         (mv consp-var $sat))))))

(defun rev-append (x y)
  (if (endp x)
      y
    (rev-append (cdr x)
                (cons (car x) y))))

(defun remove-alist-entry (key alist ans)
  (cond
   ((endp alist)
    ans)
   ((equal (caar alist) key)
    (rev-append (cdr alist) ans))
   (t
    (remove-alist-entry key (cdr alist) (cons (car alist) ans)))))

;; Remove the first equality, representing (eq i0 i1),
;; in i0's alist.
(defun delete-first-equality (i0 $sat)
  (declare (xargs :stobjs $sat))
  (update-eq-alist-vari i0
                        (cdr (eq-alist-vari i0 $sat))
                        $sat))

(defconst *f-true* t)
(defconst *f-false* nil)


(defun contains-non-const-eqp (var $sat)
  (declare (xargs :stobjs $sat))
  (not (eq (eq-alist-vari var $sat) nil)))

;; Get the i-var associated with (car var),
;; creating one if it doesn't already exist.
(defun get-car-var (var $sat)
  (declare (xargs :stobjs $sat))
  (let ((car-var (car-vari var $sat)))
    (if (valid-varp car-var)
        (mv car-var $sat)
      (mv-let
       (car-var $sat)
       (++i-var $sat)
       (let* (($sat (update-car-vari var car-var $sat))
              ($sat (update-cons-vari car-var var $sat)))
         (mv car-var $sat))))))

(defun get-cdr-var (var $sat)
  (declare (xargs :stobjs $sat))
  (let ((cdr-var (cdr-vari var $sat)))
    (if (valid-varp cdr-var)
        (mv cdr-var $sat)
      (mv-let
       (cdr-var $sat)
       (++i-var $sat)
       (let* (($sat (update-cdr-vari var cdr-var $sat))
              ($sat (update-cons-vari cdr-var var $sat)))
         (mv cdr-var $sat))))))

(defun pop-traversal-var ($sat)
  (declare (xargs :stobjs $sat))
  (let ((var-stack (var-stack $sat)))
    (cond
     ((endp var-stack)
      (let ((top-var-stack (top-var-stack $sat)))
        (cond
         ((endp top-var-stack)
          (mv nil nil $sat))
         (t
          (let* (($sat (update-top-var-stack (cdr top-var-stack) $sat))
                 (var (car top-var-stack))
                 ($sat (update-stack-numi var 0 $sat))
                 (traversal-number (1+ (traversal-number $sat)))
                 ($sat (update-traversal-number traversal-number $sat))
                 ($sat (update-traversal-numi var traversal-number $sat))
                 ($sat (update-top-completed-var-list (cons var (top-completed-var-list $sat))
                                                      $sat)))
            (mv t var $sat))))))
     (t
      ;; When a variable is popped off the stack it is added
      ;; to the completed-var-list so that we can recreate
      ;; the stack if needed.
      (let* (($sat (update-var-stack (cdr var-stack) $sat))
             (var (car var-stack))
             ($sat (update-stack-numi var 0 $sat))
             (traversal-number (1+ (traversal-number $sat)))
             ($sat (update-traversal-number traversal-number $sat))
             ($sat (update-traversal-numi var traversal-number $sat))
             ($sat (update-completed-var-list (cons var (completed-var-list $sat))
                                              $sat)))
        (mv nil var $sat))))))

;; Push a variable onto the stack and update the
;; stack num for the variable to reflect when it was
;; added.
(defun push-defined-traversal-var (var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((stack-number (1+ (stack-number $sat)))
         ($sat (update-stack-number stack-number $sat))
         ($sat (update-stack-numi var stack-number $sat))
         (var-stack (cons var (var-stack $sat))))
    (update-var-stack var-stack $sat)))

(defun push-top-traversal-var (var $sat)
  (declare (xargs :stobjs $sat))
  (let* ((stack-number (1+ (stack-number $sat)))
         ($sat (update-top-var-eqli var 1 $sat))
         ($sat (update-stack-number stack-number $sat))
         ($sat (update-stack-numi var stack-number $sat))
         (top-var-stack (cons var (top-var-stack $sat))))
    (update-top-var-stack top-var-stack $sat)))

(defun logical-car (x)
  (if (consp x) (car x) nil))

(defun logical-cdr (x)
  (if (consp x) (cdr x) nil))

(defun constrained-fnp (fn state)
  (cond
   ((consp fn)
    nil)
   (t (getprop fn
               'acl2::constrainedp
               nil
               'acl2::current-acl2-world
               (w state)))))

;; A function is uninterpreted if it is a defstub or if it has been
;; marked by the user as (to be treated as) uninterpreted.
(defun uninterpreted-fnp (fn $sat state)
  (declare (xargs :stobjs $sat))
  (cond
   ((consp fn)
    nil)
   ((getprop fn 'uninterpreted-functionp nil 'props-world
             (props-world $sat))
    t)
   (t
    (and (getprop fn 'acl2::constrainedp nil 'acl2::current-acl2-world (w state))
         (eq nil
             (getprop fn
                      'acl2::constraint-lst
                      t
                      'acl2::current-acl2-world
                      (w state)))))))

(defun set-un-fn-mark (fn val $sat)
  (declare (xargs :stobjs $sat))
  (update-props-world
   (putprop fn 'uninterpreted-functionp val (props-world $sat))
   $sat))

(defun on-stackp (ivar $sat)
  (declare (xargs :stobjs $sat))
  (not (equal (stack-numi ivar $sat) 0)))

;; Should only be used on top-level intermediate variables---e.g.
;; There is not some i2 s.t. i0 does represents (car i2).

(defun traversed-prior-top (i0 i1 $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((top-varp i0 $sat)
    (cond
     ((top-varp i1 $sat)
      (< i1 i0))
     (t
      ;; i1 will be traversed prior to i0.
      nil)))
   ((top-varp i1 $sat)
    ;; i0 will be traversed prior to i1.
    t)
   ((on-stackp i0 $sat)
    (cond
     ((on-stackp i1 $sat)
      (< (stack-numi i1 $sat) (stack-numi i0 $sat)))
     (t
      ;; i1 has been traversed, but not i0
      nil)))
   ((on-stackp i1 $sat)
    ;; i0 has been traversed, but not i1
    t)
   (t
    ;; Both have been traversed.
    (< (traversal-numi i0 $sat) (traversal-numi i1 $sat)))))

(defun get-cons-structure (i0 acc $sat)
  (declare (xargs :stobjs $sat))
  (let ((cons-var (cons-vari i0 $sat)))
    (cond
     ((not (valid-varp cons-var))
      (mv i0 acc))
     ((equal i0 (car-vari cons-var $sat))
      (get-cons-structure cons-var
                          (cons 'car acc)
                          $sat))
     (t
      (get-cons-structure cons-var
                          (cons 'cdr acc)
                          $sat)))))

(defun traversed-prior-cons (i0-car-cdr-list i1-car-cdr-list)
  (cond
   ((or (endp i0-car-cdr-list) (endp i1-car-cdr-list))
    ;; One is a subset of the other.  If i1 has no elements
    ;; left, then it's the bigger of the two (e.g. i0 = (car i1))
    ;; and therefore i0 was traversed first.
    (mv t (endp i1-car-cdr-list)))
   ((eq (car i0-car-cdr-list) (car i1-car-cdr-list))
    (traversed-prior-cons (cdr i0-car-cdr-list) (cdr i1-car-cdr-list)))
   (t
    ;; Cdr is traversed before car.
    (mv nil (eq (car i0-car-cdr-list) 'cdr)))))

;; Returns a two-tuple: (mv <subsetp> <i0-pt-i1>), where
;; <i0-pt-i1> is a Boolean that is true if i0 is or will be
;; traversed prior to i1.  Subsetp is a Boolean that
;; is true if one of the structures is a subset of the other
;; ---e.g. i0 = (car i1).

;; Note that for any iN, (cdr iN) is considered traversed prior
;; to (car iN), which is traversed prior to iN.  This is not
;; entirely accurate as we actually traverse (car iN) and (cdr iN)
;; at the same time.  However, the one place it matters, in
;; eq-todo-to-cnf, we do it right!

(defun traversed-prior (i0 i1 $sat)
  (declare (xargs :stobjs $sat))
  (mv-let
   (i0-top i0-car-cdr-list)
   (get-cons-structure i0 nil $sat)
   (mv-let
    (i1-top i1-car-cdr-list)
    (get-cons-structure i1 nil $sat)
    (cond
     ((equal i0-top i1-top)
      (traversed-prior-cons i0-car-cdr-list i1-car-cdr-list))
     (t
      (mv nil (traversed-prior-top i0-top i1-top $sat)))))))


;; Return the f-variable that represents (eq i0 i1) or
;; return an invalid variable if it doesn't exist.
(defun lookup-eq-var (i0 i1 $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal i0 i1)
    ;; If i0 is i1, then (eq x x)!.
    *f-true*)
   (t
    (mv-let
     (subsetp i0-pt-i1)
     (traversed-prior i0 i1 $sat)
     (cond
      (subsetp
       ;; (equal i0 (car i0))=>(eq i0 nil)
       (if i0-pt-i1
           (eq-nil-vari i1 $sat)
         (eq-nil-vari i0 $sat)))
      (i0-pt-i1
       (let* ((eq-alist (eq-alist-vari i0 $sat))
              (eq-entry (assoc-equal i1 eq-alist)))
         (if eq-entry (cdr eq-entry) 0)))
      (t
       (let* ((eq-alist (eq-alist-vari i1 $sat))
              (eq-entry (assoc-equal i0 eq-alist)))
         (if eq-entry (cdr eq-entry) 0))))))))

(defun create-eq-var1 (i0 i1 $sat)
  (declare (xargs :stobjs $sat))
  (let* ((eq-alist (eq-alist-vari i0 $sat))
         (eq-entry (assoc-equal i1 eq-alist)))
    (cond
     (eq-entry
      ;; If we already have an entry, return it.
      (mv (cdr eq-entry) $sat))
     (t
      ;; Otherwise, create a new variable
      ;; to represent this equality.
      (mv-let
       (f-var $sat)
       (++f-var $sat)
       (let* (($sat (update-eq-alist-vari
                     i0
                     (cons (cons i1 f-var) (eq-alist-vari i0 $sat))
                     $sat))
              ($sat (mark-ivar-relevant i0 $sat)))
         (mv f-var $sat)))))))

;; Return the f-variable that represents (eq i0 i1) or
;; create one if it doesn't exist
(defun create-eq-var (i0 i1 $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((equal i0 i1)
    ;; If i0 is i1, then (eq x x)!.
    (mv *f-true* $sat))
   (t
    (mv-let
     (subsetp i0-pt-i1)
     (traversed-prior i0 i1 $sat)
     (cond
      (subsetp
       ;; (equal i2 (car i2))=>(eq i2 nil)
       (if i0-pt-i1
           (create-eq-nil-var i1 $sat)
         (create-eq-nil-var i0 $sat)))
      (i0-pt-i1
       (create-eq-var1 i0 i1 $sat))
      (t
       (create-eq-var1 i1 i0 $sat)))))))

(defun quote-list (x acc)
  (cond
   ((endp x)
    (revappend acc nil))
   (t
    (quote-list (cdr x)
                (cons `(quote ,(car x))
                      acc)))))

(defun ce-val-unknownp (val)
  ;;!! Note once we switch to ACL2 3.0.1 we won't need the
  ;; double quote!
  (or (equal '(quote sat::unknown) val)
      (eq 'sat::unknown val)))

(defun ce-val-unknown-listp (val-list)
  (cond
   ((endp val-list)
    nil)
   ((ce-val-unknownp (car val-list))
    t)
   (t
    (ce-val-unknown-listp (cdr val-list)))))

(defun ce-val-consp (x)
  (cond
   ((ce-val-unknownp x)
    'sat::unknown)
   (t
    (consp x))))

(defun ce-val-cons (x y)
  (cond
   ((or (ce-val-unknownp x)
        (ce-val-unknownp y))
    'sat::unknown)
   (t
    (cons x y))))

(defun ce-val-equal (x y)
  (cond
   ((or (ce-val-unknownp x)
        (ce-val-unknownp y))
    'sat::unknown)
   (t
    (equal x y))))

(defun print-msg (verbosity msg $sat)
  (declare (xargs :stobjs $sat))
  (if (> verbosity (verbosity $sat))
      nil
    (fmt-to-comment-window (car msg) (cdr msg) 0 nil nil)))



