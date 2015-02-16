; The SEQ Macro Language
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "../../util/warnings")

(defsection seq
  ;; BOZO not really a macro library, need somewhere better to put this
  :parents (parser)
  :short "A variant of @(see acl2::seq) for use in VL's parser.")

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

  (b* (((mv nametree type action)
        (if (member-eq (first x) '(:= :w= :s=))
            (mv nil (first x) (second x))
          (mv (first x) (second x) (third x))))
       (rest `(check-vars-not-free (!!!error !!!val)
                                   ,rest))
       (body (cond ((not nametree) rest)
                   ((symbolp nametree)
                    `(let ((,nametree !!!val)) ,rest))
                   (t
                    `(let ,(seq-nametree-to-let-bindings nametree '!!!val)
                       ,rest)))))
    (if (eq type :=)
        `(mv-let (!!!error !!!val ,stream)
           ,action
           (if !!!error
               (mv !!!error !!!val ,stream)
             ,body))
      `(let ((!!!tokens (vl-tokstream->tokens)))
         (mv-let (!!!error !!!val ,stream)
           ,action
           (cond (!!!error
                  (mv !!!error !!!val ,stream))
                 ((not (mbt (,(case type (:s= '<) (:w= '<=))
                             (len (vl-tokstream->tokens))
                             (len !!!tokens))))
                  (prog2$ (er hard? "SEQ count failed for (~x0 ~x1.)~%"
                              ',type ',action)
                          (mv (make-vl-warning :type :vl-seq-fail
                                               :msg "SEQ count failure."
                                               :fatalp t)
                              nil
                              ,stream)))
                 (t ,body)))))))

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

(defun seq-backtrack-aux (stream blocks)
  (declare (xargs :guard (and (seq-name-p stream)
                              (seq-block-list-p blocks t)
                              (consp blocks))))
  (if (atom (cdr blocks))
      `(seq ,stream . ,(car blocks))
    `(b* (((mv !!!error !!!val ,stream)
           (check-vars-not-free (!!!backup)
                                (seq ,stream . ,(car blocks))))
          ((unless !!!error)
           (mv !!!error !!!val ,stream))
          (,stream (vl-tokstream-restore !!!backup)))
       (check-vars-not-free
        (!!!error !!!val)
        ,(seq-backtrack-aux stream (cdr blocks))))))

(defun seq-backtrack-fn (stream blocks)
  (declare (xargs :guard (and (seq-name-p stream)
                              (seq-block-list-p blocks t)
                              (consp blocks))))
  (if (atom (cdr blocks))
      `(seq ,stream . ,(car blocks))
    `(b* ((!!!backup (vl-tokstream-save)))
       ,(seq-backtrack-aux stream blocks))))

(defmacro seq-backtrack (stream &rest blocks)
  (seq-backtrack-fn stream blocks))

