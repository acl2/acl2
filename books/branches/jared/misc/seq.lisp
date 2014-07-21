; The SEQ Macro Language
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection seq
  ;; BOZO not really a macro library, need somewhere better to put this
  :parents (macro-libraries)
  :short "<i>Seq</i> is a macro language for applying actions to a stream."

  :long "<p>In this context, a <i>stream</i> is any data structure that we want
to update in an essentially sequential/single-threaded way.  It might be a
stobj, but it could also be a regular ACL2 list or some other kind of
structure.  For example, in the @(see vl) Verilog parser, we typically use seq
to traverse a list of tokens, which are regular ACL2 objects.</p>

<p>Meanwhile, an <i>action</i> is some operation which typically inspects the
stream, and then returns a triple of the form @('(mv error val stream)').  When
the action is successful, @('error') is @('nil'), @('stream') is the updated
stream, and @('val') is perhaps some piece of information that was gleaned from
running this action.  For instance, in the Verilog parser we may take a token
out of the stream and put it into val.</p>

<p>But an action may also fail, in which case it should set @('error') to some
non-nil value, typically an error message produced by @(see msg).</p>

<p>A Seq program is introduced by writing:</p>

@({
    (seq <stream> ... statements ...)
})

<p>Where @('stream') is the name of the stream to operate on and update, and
the valid statements are described below.  Every Seq program evaluates to an
@('(mv error val stream)') triple.</p>

<p>Some examples of using Seq can be found in @('misc/seq-examples.lsp').</p>


<h3>The Basic Assignment Statement</h3>

<p>In many ways, Seq resembles a loop-free, imperative programming language
with a mechanism to throw exceptions.  Seq programs are written as blocks of
statements, and the fundamental statement is assignment:</p>

@({
    (var := (action ... <stream>))
})

<p>Such an assignment statement has two effects when action is successful:</p>

<ol>
<li>It binds var to the val produced by the action, and</li>
<li>It rebinds stream to the updated stream produced by the action</li>
</ol>

<p>But action may also fail, in which case the failure stops execution of the
current block and we propagate the error upwards throughout the entire Seq
program.</p>


<h3>Alternative Forms of Assignment</h3>

<p>We have a couple of additional assignment statements.  The first variant
simply allows you to ignore the val produced by an action, and is written:</p>

@({
     (:= (action ... <stream>))
})

<p>The second variant allows you to destructure the val produced by the action,
and is written:</p>

@({
     ((foo . bar) := (action ... <stream>))
})

<p>@('NIL') has a special meaning in this second form, and can be used to
\"drop\" parts of val which are not interesting.  For example, if action
produces the value (1 . 2), and you write:</p>

@({
     ((foo . nil) := action)
})

<p>Then @('foo') will be bound to 1 and the \"2\" part of val will be
inaccessible.</p>

<p>(Usually unnecessary): In place of @(':=') in any of the above, one can also
write:</p>

<ul>
<li>@(':w=') &mdash; weak count decrease</li>
<li>@(':s=') &mdash; strong count decrease</li>
</ul>

<p>These act the same as @(':='), except that they add some @('(mbe :logic
...)')-only checks that ensure that the returned stream has a weakly lower or
strongly lower @(see acl2-count) than the stream going into the action.  This
is sometimes needed when using Seq in mutually-recursive functions.</p>


<h3>Conditional Execution</h3>

<p>A block can be only conditionally executed by wrapping it in a <b>when</b>
or <b>unless</b> clause.  For example:</p>

@({
    (when (integerp x)
      (foo := (action1 ...)
      (bar := (action2 ...)))

    (unless (consp x)
      (foo := (action ...)))
})

<p>This causes the bindings for @('foo') and @('bar') only to be executed when
the condition evaluates to non-@('nil').</p>


<h3>Return Statements</h3>

<p>The final statement of a Seq program must be a return statement, and \"early\"
return statements can also occur as the last statement of a when or unless
block.  There are two versions of the return statement.</p>

@({
    (return expr)
    (return-raw action)
})

<p>Either one of these causes the entire Seq program to exit.  In the first
form, @('expr') is expected to evaluate to a regular ACL2 object, and the result
of the Seq program will be @('(mv nil expr stream)').</p>

<p>In the second form, @('action') is expected to itself evaluate to an @('(mv
error val stream)') tuple, and the Seq program returns this value verbatim.</p>


<h3>Backtracking</h3>

<p>We also provide another macro, <b>seq-backtrack</b>, which cannot be used on
STOBJs, but can be used with regular, applicative structures.  The general form
is:</p>

@({
    (seq-backtrack stream block1 block2 ...)
})

<p>This macro has the following effect.  First, we try to run @('block1').  If
it succeeds, we return the @('(mv error val new-stream)') that it returns.
Otherwise, we start again with the initial @('stream') and try to run the
remaining blocks, in order.  If none of the blocks succeed, we return the
@('(mv error val new-stream)') encountered by the final block.</p>


<h3>Other Resources</h3>

<p>While Seq is convenient in certain cases, the @(see b*) macro is generally
more flexible.</p>

<p>See also @(see seqw), an expanded version of @(see seq) that supports the
creation of warnings while processing the stream.</p>")

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
                                        (len ,stream)
                                        (len !!!stream))))
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
                                               (len ,stream)
                                               (len !!!stream))))
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
                                             (len ,stream)
                                             (len !!!stream))))
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

