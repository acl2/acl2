; The SEQ Macro Language
; Copyright (C) 2008-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")


; THE SEQ MACRO
;
; NOTE: See seq-examples.lsp for some examples.
; NOTE: See seqw.lisp for an expanded version of SEQ.
;
; SEQ is a macro language for applying ACTIONS to a STREAM.
;
; In this context, a "stream" is any data structure that we want to update in
; an essentially sequential/single-threaded way.  It might be a stobj, but it
; could also be a regular ACL2 list or some other kind of structure.  For
; example, in the Verilog parser we typically use seq to traverse a list of
; tokens, which are regular ACL2 objects.
;
; Meanwhile, an "action" is some operation which typically inspects the stream,
; and then returns a triple of the form (MV ERROR VAL STREAM).  When the action
; is successful, ERROR is nil, STREAM is the updated stream, and VAL is perhaps
; some piece of information that was gleaned from running this action.  For
; instance, in the Verilog parser we may take a token out of the stream and put
; it into val.
;
; But an action may also fail, in which case it should set ERROR to some
; non-nil value.  Generally, we cons together a list of the form
;
;   (fmt-str arg0 arg1 ... argN)
;
; Where these arguments are just like in calls to "cw."  Assuming we have saved
; such an object in "x", we would typically print it using (cw-obj x), which is
; defined below.
;
; A SEQ program is introduced by writing:
;    (SEQ <stream> ... statements ...)
;
; Where stream is the name of the stream to operate on and update, and the
; valid statements are described below.  Every SEQ program evaluates to an (MV
; ERROR VAL STREAM) triple.
;
;
;
; THE BASIC ASSIGNMENT STATEMENT
;
; In many ways, SEQ resembles a loop-free, imperative programming language with
; a mechanism to throw exceptions.  SEQ programs are written as blocks of
; statements, and the fundamental statement is assignment:
;
;    (var := (action ... <stream>))
;
; Such an assignment statement has two effects when action is successful:
;
;   1. It binds var to the val produced by the action, and
;   2. It rebinds stream to the updated stream produced by the action
;
; But action may also fail, in which case the failure stops execution of the
; current block and we propagate the error upwards throughout the entire SEQ
; program.
;
;
;
; ALTERNATIVE FORMS OF ASSIGNMENT
;
; We have a couple of additional assignment statements.  The first variant
; simply allows you to ignore the val produced by an action, and is written:
;
;     (:= (action ... <stream>))
;
; The second variant allows you to destructure the val produced by the action,
; and is written:
;
;     ((foo . bar) := (action ... <stream>))
;
; NIL has a special meaning in this second form, and can be used to "drop"
; parts of val which are not interesting.  For example, if action produces
; the value (1 . 2), and you write:
;
;     ((foo . nil) := action)
;
; Then foo will be bound to 1 and the "2" part of val will be inaccessible.
;
; (Usually unnecessary): In place of := in any of the above, one can also write:
;
;   :w=  -- "weak count decrease"
;   :s=  -- "strong count decrease"
;
; These act the same as :=, except that they add some (mbe :logic ...)-only
; checks that ensure that the returned stream has a weakly lower or strongly
; lower ACL2 count than the stream going into the action.  This is sometimes
; needed when using seq in mutually-recursive functions.
;
;
;
;
; CONDITIONAL EXECUTION
;
; A block can be only conditionally executed by wrapping it in a WHEN or UNLESS
; clause.  For example:
;
;    (when (integerp x)
;      (foo := (action1 ...)
;      (bar := (action2 ...)))
;
;    (unless (consp x)
;      (foo := (action ...)))
;
; This causes the bindings for foo and bar only to be executed when the
; condition evaluates to non-nil.
;
;
;
; RETURN STATEMENTS
;
; The final statement of a SEQ program must be a return statement, and "early"
; return statements can also occur as the last statement of a when or unless
; block.  There are two versions of the return statement.
;
;    (return expr)
;    (return-raw action)
;
; Either one of these causes the entire SEQ program to exit.  In the first
; form, EXPR is expected to evaluate to a regular ACL2 object, and the result
; of the SEQ program will be (MV NIL EXPR STREAM).  In the second form, ACTION
; is expected to itself evaluate to an (MV ERROR VAL STREAM) tuple, and the
; SEQ program returns this value verbatim.
;
;
;
; BACKTRACKING
;
; We also provide another macro, SEQ-BACKTRACK, which cannot be used on STOBJs,
; but can be used with regular, applicative structures.  The general form is:
;
;    (SEQ-BACKTRACK STREAM BLOCK1 BLOCK2 ...)
;
; This macro has the following effect.  First, we try to run BLOCK1.  If it
; succeeds, we return the (MV ERROR VAL NEW-STREAM) that it returns.
; Otherwise, we start again with the initial STREAM and try to run the
; remaining blocks, in order.  If none of the blocks succeed, we return the (MV
; ERROR VAL NEW-STREAM) encountered by the final block.

(encapsulate
 ()
 (defund make-cw-obj-alist (x n)
   (declare (xargs :guard (natp n)
                   :verify-guards nil))
   (if (atom x)
       nil
     (acons (case n
              (0 #\0) (1 #\1) (2 #\2) (3 #\3) (4 #\4)
              (5 #\5) (6 #\6) (7 #\7) (8 #\8) (9 #\9)
              (otherwise
               (er hard? 'cw-obj "Like cw, cw-obj is limited to 10 objects.")))
            (car x)
            (make-cw-obj-alist (cdr x) (1+ n)))))

 (defthm alistp-of-make-cw-obj-alist
   (alistp (make-cw-obj-alist x n))
   :hints(("Goal" :in-theory (enable make-cw-obj-alist))))

 (verify-guards make-cw-obj-alist)

 (defund cw-obj (x)
   ;; This is a "lazy" version of cw.
   ;; For instance,
   ;;   (cw-obj (list "hello, ~x0~%" 5)) prints Hello, 5 followed by a newline.
   ;; Note that it may cause an error.
   (declare (xargs :guard t))
   (and (or (consp x)
            (er hard? 'cw-obj "Expected a cons, but got ~x0.~%" x))
        (or (stringp (car x))
            (er hard? 'cw-obj "Expected a fmt-string as the first arg, but got ~x0.~%" (car x)))
        (fmt-to-comment-window (car x)
                               (make-cw-obj-alist (cdr x) 0)
                               0
                               nil)))

 (defthm cw-obj-is-nil
   (equal (cw-obj x) nil)
   :rule-classes :definition))



(program)



; NAMETREES
;
; Nametrees are trees of variable names and nils which contain no duplicate
; names.  They are used to give us automatic destructing of values returned by
; actions in our binding statements.

(defun seq-name-p (x)
  (declare (xargs :guard t))
  (cond ((not (symbolp x))
         (cw "Error: ~x0 cannot be used as a variable name.~%" x))
        ((eq x t)
         (cw "Error: t cannot be used as a variable name.~%"))
        ((equal (symbol-package-name x) "KEYWORD")
         (cw "Error: ~x0 cannot be used as a variable name.~%" x))
        (t t)))

(defun seq-aux-nametree-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (seq-aux-nametree-p (car x))
           (seq-aux-nametree-p (cdr x)))
    (seq-name-p x)))

(defun seq-flatten-nametree (x)
  (declare (xargs :guard (seq-aux-nametree-p x)))
  (if (consp x)
      (append (seq-flatten-nametree (car x))
              (seq-flatten-nametree (cdr x)))
    (if (not x)
        nil
      (list x))))

(defun seq-nametree-p (x)
  (declare (xargs :guard t))
  (and (seq-aux-nametree-p x)
       (or (no-duplicatesp (seq-flatten-nametree x))
           (cw "Error: the nametree ~x0 contains duplicates.~%" x))))

(defun seq-nametree-to-let-bindings (x path)
  (declare (xargs :guard (seq-nametree-p x)))
  (if (consp x)
      (append (seq-nametree-to-let-bindings (car x) `(car ,path))
              (seq-nametree-to-let-bindings (cdr x) `(cdr ,path)))
    (if (not x)
        nil
      (list (list x path)))))





(defun seq-bind-p (x)

; The binding statements are:
;
;   1. (:= ACTION)
;   2. (NAMETREE := ACTION)

  (declare (xargs :guard t))
  (and (consp x)
       (if (member-eq (first x) '(:= :w= :s=))
           (and (or (true-listp x)
                    (cw "Error: Expected assignment to be a true-listp. ~x0.~%" x))
                (or (= (length x) 2)
                    (cw "Error: Expected assignment to have length 2. ~x0.~%" x)))
         (and (consp (cdr x))
              (member-eq (second x) '(:= :w= :s=))
              (or (true-listp x)
                  (cw "Error: Expected assignment to be a true-listp. ~x0.~%" x))
              (or (= (length x) 3)
                  (cw "Error: Expected assignment to have length 3. ~x0.~%" x))
              (or (seq-nametree-p (first x))
                  (cw "Error: Expected assignment to have a name-tree. ~x0.~%" x))))))


(defun seq-return-p (x)

; The return statements are:
;
;   1. (RETURN EXPR)
;   2. (RETURN-RAW ACTION)
;

  (declare (xargs :guard t))
  (and (consp x)
       (or (eq (car x) 'return)
           (eq (car x) 'return-raw))
       (or (true-listp x)
           (cw "Error: Expected return to be a true-listp. ~x0.~%" x))
       (or (= (length x) 2)
           (cw "Error: Expected return to have length 2. ~x0.~%" x))))

(mutual-recursion

 (defun seq-when-p (x)

; The when statement has the form:
;
;    (WHEN CONDITION &rest BLOCK)
;
; Where CONDITION is an ACL2 expression that evalutes to a single, ACL2 object.
; This object is interpreted as a boolean, i.e., condition is said to be met if
; the object is non-nil.
;
; The block is skipped unless the condition is met.  The block may end with a
; return statement to cause an early return from any enclosing blocks.

   (declare (xargs :guard t))
   (and (consp x)
        (eq (car x) 'when)
        (or (true-listp x)
            (cw "Error: \"when\" must be a true-listp. ~x0.~%" x))
        (or (>= (length x) 3)
            (cw "Error: \"when\" must have at least length 3. ~x0.~%" x))
        (seq-block-p (cddr x) nil)))

 (defun seq-unless-p (x)

; The unless statement has the form:
;
;    (UNLESS CONDITION &rest BLOCK)
;
; And is simply an alias for (WHEN (NOT CONDITION) &rest BLOCK)

   (declare (xargs :guard t))
   (and (consp x)
        (eq (car x) 'unless)
        (or (true-listp x)
            (cw "Error: \"unless\" must be a true-listp. ~x0.~%" x))
        (or (>= (length x) 3)
            (cw "Error: \"unless\" must have at least length 3. ~x0.~%" x))
        (seq-block-p (cddr x) nil)))

 (defun seq-block-p (x toplevelp)

; A block is a list of other statements.  A top-level block must end with
; a return statement, but other blocks need not do so.

   (declare (xargs :guard t))
   (cond ((atom x)
          (cw "Error: expected a block, but found ~x0.~%" x))
         ((atom (cdr x))
          (if toplevelp
              (or (seq-return-p (car x))
                  (cw "Error: top-level block must end with a return ~
                       statement, but ends with ~x0.~%" x))
            (or (seq-bind-p (car x))
                (seq-when-p (car x))
                (seq-unless-p (car x))
                (seq-return-p (car x))
                (cw "Error: invalid final block statement: ~x0.~%" (car x)))))
         (t
          (and (or (seq-bind-p (car x))
                   (seq-when-p (car x))
                   (seq-unless-p (car x))
                   (cw "Error: invalid interior block statement: ~x0.~%" (car x)))
               (seq-block-p (cdr x) toplevelp))))))




; BOUND NAMES
;
; We write functions to collect all of the names found in any NAMETREE within a
; statement or block.  These names are needed in order to handle WHEN and
; UNLESS statements without early returns, and to set up the initial lexical
; environment for the block.

(defun seq-bind-names (x)
  (declare (xargs :guard (seq-bind-p x)))
  (if (member-eq (car x) '(:= :w= :s=))
      nil
    (seq-flatten-nametree (first x))))

(mutual-recursion

 (defun seq-when-names (x)
   (declare (xargs :guard (seq-when-p x)))
   (seq-block-names (cddr x) nil))

 (defun seq-unless-names (x)
   (declare (xargs :guard (seq-unless-p x)))
   (seq-block-names (cddr x) nil))

 (defun seq-stmt-names (x)
   (declare (xargs :guard (or (seq-bind-p x)
                              (seq-when-p x)
                              (seq-unless-p x)
                              (seq-return-p x))))
   (cond ((seq-bind-p x) (seq-bind-names x))
         ((seq-when-p x) (seq-when-names x))
         ((seq-unless-p x) (seq-unless-names x))
         ((seq-return-p x) nil)))

 (defun seq-block-names (x toplevelp)
   (declare (xargs :guard (seq-block-p x toplevelp)))
   (if (atom (cdr x))
       (seq-stmt-names (car x))
     (append (seq-stmt-names (car x))
             (seq-block-names (cdr x) toplevelp)))))




(defun seq-process-bind (x stream rest)

; X is a bind statement, stream is the name of the stream we are processing,
; and rest is the expansion of the rest of the lines in the block.  We are to
; write the MV code for this bind statement.

  (declare (xargs :guard (and (seq-bind-p x)
                              (seq-name-p stream))))

  (cond ((eq (car x) :=)
         (let ((action (second x)))
           `(mv-let (!!!error !!!val ,stream)
                    ,action
                    (if !!!error
                        (mv !!!error !!!val ,stream)
                      (check-vars-not-free (!!!error !!!val !!!stream)
                                           ,rest)))))

        ((or (eq (car x) :w=)
             (eq (car x) :s=))
         (let ((action (second x)))
           `(let ((!!!stream ,stream))
              (mv-let (!!!error !!!val ,stream)
                      ,action
                      (cond (!!!error
                             (mv !!!error !!!val ,stream))
                            ((not (mbt (,(case (car x) (:s= '<) (:w= '<=))
                                        (acl2-count ,stream)
                                        (acl2-count !!!stream))))
                             (prog2$ (er hard? "SEQ count failed for (~x0 ~x1.)~%"
                                         ',(car x) ',action)
                                     (mv "SEQ count failure." nil !!!stream)))
                            (t
                             (check-vars-not-free (!!!error !!!val !!!stream)
                                                  ,rest)))))))

        (t
         (let* ((nametree (first x))
                (type     (second x))
                (action   (third x)))
           (if (and nametree (symbolp nametree))
               ;; We have only a single variable.  We can write some cleaner
               ;; mv-let code without any of this nametree destucturing.

               (case type

                 (:= `(mv-let (!!!error ,nametree ,stream)
                              ,action
                              (if !!!error
                                  (mv !!!error ,nametree ,stream)
                                (check-vars-not-free (!!!error !!!val !!!stream) ,rest))))

                 ((:w= :s=)
                  `(let ((!!!stream ,stream))
                     (mv-let (!!!error ,nametree ,stream)
                             ,action
                             (cond (!!!error
                                    (mv !!!error ,nametree ,stream))
                                   ((not (mbt (,(case type (:s= '<) (:w= '<=))
                                               (acl2-count ,stream)
                                               (acl2-count !!!stream))))
                                    (prog2$ (er hard? "SEQ count failed for (~x0 ~x1 ~x2.)~%"
                                                ',nametree ',type ',action)
                                            (mv "SEQ count failure." nil !!!stream)))
                                   (t
                                    (check-vars-not-free (!!!error !!!val !!!stream) ,rest)))))))

             ;; Multiple variables; do the destructuring.
             (case type

               (:= `(mv-let (!!!error !!!val ,stream)
                            ,action
                            (if !!!error
                                (mv !!!error !!!val ,stream)
                              (let ,(seq-nametree-to-let-bindings nametree '!!!val)
                                (check-vars-not-free (!!!error !!!val !!!stream)
                                                     ,rest)))))

               ((:w= :s=)
                `(let ((!!!stream ,stream))
                   (mv-let (!!!error !!!val ,stream)
                           ,action
                           (cond (!!!error
                                  (mv !!!error !!!val ,stream))
                                 ((not (mbt (,(case type (:s= '<) (:w= '<=))
                                             (acl2-count ,stream)
                                             (acl2-count !!!stream))))
                                  (prog2$ (er hard?  "SEQ count failed for (~x0 ~x1 ~x2.)~%"
                                              ',nametree ',type ',action)
                                          (mv "SEQ count failure." nil !!!stream)))
                                 (t
                                  (let ,(seq-nametree-to-let-bindings nametree '!!!val)
                                    (check-vars-not-free (!!!error !!!val !!!stream) ,rest)))))))))))))

;(seq-process-bind '(:= action) 'stream '<rest>)
;(seq-process-bind '(foo := action) 'stream '<rest>)
;(seq-process-bind '((foo . bar) := action) 'stream '<rest>)
;(seq-process-bind '((foo . nil) := action) 'stream '<rest>)


(defun seq-list-ends-with-returnp (x)
  (declare (xargs :guard (consp x)))
  (if (atom (cdr x))
      (seq-return-p (car x))
    (seq-list-ends-with-returnp (cdr x))))

;(seq-list-ends-with-returnp '(1 2 3))
;(seq-list-ends-with-returnp '(1 2 (return 3)))


(defun seq-make-let-pairs-for-when (names)
  (declare (xargs :guard t))
  (cond ((atom names)
         nil)
        ((atom (cdr names))
         (list `(,(car names) (car !!!val))))
        (t
         (list* `(,(car names) (car !!!val))
                `(!!!val       (cdr !!!val))
                (seq-make-let-pairs-for-when (cdr names))))))

;(seq-make-let-pairs-for-when '(a b c))
;(seq-make-let-pairs-for-when nil)

(mutual-recursion

 (defun seq-process-unless (x stream rest)

; Unless statements are easily transformed into when statements.

   (declare (xargs :guard (and (seq-unless-p x)
                               (seq-name-p stream))))
   (let ((condition (second x))
         (subblock  (cddr x)))
     (seq-process-when (list* 'when
                              `(not ,condition)
                              subblock)
                       stream rest)))


 (defun seq-process-when (x stream rest)

; X is a when statement, stream is the name of the stream we are processing,
; and rest is the expansion for the statements that come after this when
; statement in the current block.  We are to write the MV code for this when
; statement.

   (declare (xargs :guard (and (seq-when-p x)
                               (seq-name-p stream))))

   (let* ((condition         (second x))
          (subblock          (cddr x))
          (ends-with-returnp (seq-list-ends-with-returnp subblock))
          (bound-in-subblock (seq-block-names subblock nil)))

     (cond

; Easy case 1.  The subblock ends with a return, so we always either process it
; or rest but never both.

      (ends-with-returnp
       `(if ,condition
            ,(seq-process-block subblock stream nil)
          ,rest))


; Easy case 2.  The subblock doesn't end with a return, so we may process it or
; and rest; but since it binds no variables so the only thing that it changes is
; the stream.

      ((not bound-in-subblock)
       `(mv-let (!!!error !!!val ,stream)
                (if ,condition
                    ,(seq-process-block subblock stream nil)
                  (mv nil nil ,stream))
                (if !!!error
                    (mv !!!error !!!val ,stream)
                  (check-vars-not-free (!!!error !!!val) ,rest))))


; Hard case.  The subblock does not end with a return.  So if the condition is
; met, we're just going to do some additional bindings and stream manipulation
; before the processing rest.  The hard part of this is dealing with all of the
; things that variables that might have been bound in the subblock.

; Our basic approach is to add a return statement to the end of the subblock
; before processing it, which returns to us a list of all the values for the
; variables it binds.  We can then rebind these variables before giving them to
; rest.

      (t
       (let* ((return-stmt       `(return (list ,@bound-in-subblock)))
              (return-expansion  `(mv nil (list ,@bound-in-subblock) ,stream))
              (new-subblock      (append subblock (list return-stmt)))
              (rebindings        (seq-make-let-pairs-for-when bound-in-subblock)))

         `(mv-let (!!!error !!!val ,stream)
                  (if ,condition
                      ,(seq-process-block new-subblock stream nil)
                    ,return-expansion)
                  (if !!!error
                      (mv !!!error !!!val ,stream)

; At this point, !!!val holds the list of all the values for the variables
; which were bound in the subblock.  We just need to redo these bindings so
; that they are available in rest.

                    (let* ,rebindings
                      (check-vars-not-free (!!!error !!!val) ,rest)))))))))

 (defun seq-process-stmt (x stream rest)
   (declare (xargs :guard (and (or (seq-bind-p x)
                                   (seq-when-p x)
                                   (seq-unless-p x)
                                   (seq-return-p x))
                               (seq-name-p stream))))
   (cond ((seq-bind-p x)
          (seq-process-bind x stream rest))
         ((seq-when-p x)
          (seq-process-when x stream rest))
         ((seq-unless-p x)
          (seq-process-unless x stream rest))
         (t
          (let ((type (first x))
                (value (second x)))
            (cond ((eq type 'return)
                   `(mv nil ,value ,stream))
                  ((eq type 'return-raw)
                   value))))))

 (defun seq-process-block (x stream toplevelp)
   (declare (xargs :guard (and (seq-block-p x toplevelp)
                               (seq-name-p stream))))
   (if (atom (cdr x))
       (seq-process-stmt (car x) stream `(mv nil nil ,stream))
     (let ((rest (seq-process-block (cdr x) stream toplevelp)))
       (seq-process-stmt (car x) stream rest)))))


(defun seq-make-initial-let-pairs (names)
  (declare (xargs :guard t))
  (if (atom names)
      nil
    (cons `(,(car names) nil)
          (seq-make-initial-let-pairs (cdr names)))))

;(seq-make-initial-let-pairs '(a b c d))

(defun seq-fn (stream block)
  (declare (xargs :guard (and (seq-name-p stream)
                              (seq-block-p block t))))
  (let* ((names            (seq-block-names block t))
         (initial-bindings (seq-make-initial-let-pairs (remove-duplicates names))))
    `(let ,initial-bindings
       (declare (ignorable ,@names))
       ,(seq-process-block block stream t))))

;(seq-fn 'tokens *hid-block*)

(defmacro seq (stream &rest block)
  (seq-fn stream block))





(defun seq-block-list-p (x toplevelp)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (seq-block-p (car x) toplevelp)
         (seq-block-list-p (cdr x) toplevelp))))

(defun seq-backtrack-fn (stream blocks)
  (declare (xargs :guard (and (seq-name-p stream)
                              (seq-block-list-p blocks t)
                              (consp blocks))))
  (if (atom (cdr blocks))
      `(seq ,stream . ,(car blocks))
    `(mv-let (!!!error !!!val updated-stream)
             (seq ,stream . ,(car blocks))
             (if (not !!!error)
                 (mv !!!error !!!val updated-stream)
               (check-vars-not-free (!!!error !!!val)
                                    ,(seq-backtrack-fn stream (cdr blocks)))))))

(defmacro seq-backtrack (stream &rest blocks)
  (seq-backtrack-fn stream blocks))

