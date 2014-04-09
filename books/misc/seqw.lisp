; The SEQW Macro Language
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "seq")

(defsection seqw
  :parents (seq)
  :short "An alternative implementation of the Seq language which allows for
warnings to be implicitly collected and stored in a list as your program
executes."

  :long "<p>As background see @(see seq); here we only describe the differences
between Seqw and Seq.</p>

<p>The difference is quite straightforward:</p>

<ul>

<li>Whereas a Seq program has the form @('(seq <stream> ...)'), a Seqw program
instead has one additional argument, @('(seqw <stream> <warnings> ...)'), where
@('<warnings>') is the name of a <i>warnings structure</i> (see below).</li>

<li>Whereas every Seq action returns @('(mv error val stream)'), each Seqw action
instead returns @('(mv error val stream warnings)'), where warnings is the
updated warnings structure.</li>

<li>Similarly, every Seqw program returns @('(mv error val stream warnings)')
instead of @('(mv error val stream)').</li>

</ul>

<p>What is a warnings structure?  When we use Seqw, we generally accumulate
warnings into a list, so our actions just cons new warnings into this list
when desired.  But Seqw itself imposes no particular constraints on what
a warnings structure is, and generally the way in which a warning is updated
is determined by the actions of the program rather than by Seqw itself.</p>

<p>For examples of using SEQW, see the file @('misc/seqw-examples.lsp').</p>")

(program)

(defun seqw-process-bind (x stream warnings rest)

; X is a bind statement, stream is the name of the stream we are processing,
; and rest is the expansion of the rest of the lines in the block.  We are to
; write the MV code for this bind statement.

  (declare (xargs :guard (and (seq-bind-p x)
                              (seq-name-p stream)
                              (seq-name-p warnings))))

  (cond ((eq (car x) :=)
         (let ((action (second x)))
           `(mv-let (!!!error !!!val ,stream ,warnings)
                    ,action
                    (if !!!error
                        (mv !!!error !!!val ,stream ,warnings)
                      (check-vars-not-free (!!!error !!!val !!!stream)
                                           ,rest)))))

        ((or (eq (car x) :w=)
             (eq (car x) :s=))
         (let ((action (second x)))
           `(let ((!!!stream ,stream))
              (mv-let (!!!error !!!val ,stream ,warnings)
                      ,action
                      (cond (!!!error
                             (mv !!!error !!!val ,stream ,warnings))
                            ((not (mbt (,(case (car x) (:s= '<) (:w= '<=))
                                        (len ,stream)
                                        (len !!!stream))))
                             (prog2$ (er hard? "SEQW count failed for (~x0 ~x1.)~%"
                                         ',(car x) ',action)
                                     (mv "SEQW count failure." nil !!!stream ,warnings)))
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

                 (:= `(mv-let (!!!error ,nametree ,stream ,warnings)
                              ,action
                              (if !!!error
                                  (mv !!!error ,nametree ,stream ,warnings)
                                (check-vars-not-free (!!!error !!!val !!!stream)
                                                     ,rest))))

                 ((:w= :s=)
                  `(let ((!!!stream ,stream))
                     (mv-let (!!!error ,nametree ,stream ,warnings)
                             ,action
                             (cond (!!!error
                                    (mv !!!error ,nametree ,stream ,warnings))
                                   ((not (mbt (,(case type (:s= '<) (:w= '<=))
                                               (len ,stream)
                                               (len !!!stream))))
                                    (prog2$ (er hard? "SEQW count failed for (~x0 ~x1 ~x2.)~%"
                                                ',nametree ',type ',action)
                                            (mv "SEQW count failure." nil !!!stream ,warnings)))
                                   (t
                                    (check-vars-not-free (!!!error !!!val !!!stream)
                                                         ,rest)))))))

             ;; Multiple variables; do the destructuring.
             (case type

               (:= `(mv-let (!!!error !!!val ,stream ,warnings)
                            ,action
                            (if !!!error
                                (mv !!!error !!!val ,stream ,warnings)
                              (let ,(seq-nametree-to-let-bindings nametree '!!!val)
                                (check-vars-not-free (!!!error !!!val !!!stream)
                                                     ,rest)))))

               ((:w= :s=)
                `(let ((!!!stream ,stream))
                   (mv-let (!!!error !!!val ,stream ,warnings)
                           ,action
                           (cond (!!!error
                                  (mv !!!error !!!val ,stream ,warnings))
                                 ((not (mbt (,(case type (:s= '<) (:w= '<=))
                                             (len ,stream)
                                             (len !!!stream))))
                                  (prog2$ (er hard?  "SEQW count failed for (~x0 ~x1 ~x2.)~%"
                                              ',nametree ',type ',action)
                                          (mv "SEQW count failure." nil !!!stream ,warnings)))
                                 (t
                                  (let ,(seq-nametree-to-let-bindings nametree '!!!val)
                                    (check-vars-not-free (!!!error !!!val !!!stream)
                                                         ,rest)))))))))))))

;(seqw-process-bind '(:= action) 'stream 'warnings '<rest>)
;(seqw-process-bind '(foo := action) 'stream 'warnings '<rest>)
;(seqw-process-bind '((foo . bar) := action) 'stream 'warnings '<rest>)
;(seqw-process-bind '((foo . nil) := action) 'stream 'warnings '<rest>)


(mutual-recursion

 (defun seqw-process-unless (x stream warnings rest)

; Unless statements are easily transformed into when statements.

   (declare (xargs :guard (and (seq-unless-p x)
                               (seq-name-p stream)
                               (seq-name-p warnings))))
   (let ((condition (second x))
         (subblock  (cddr x)))
     (seqw-process-when (list* 'when
                               `(not ,condition)
                               subblock)
                        stream warnings rest)))


 (defun seqw-process-when (x stream warnings rest)

; X is a when statement, stream is the name of the stream we are processing,
; warnings is the name of the warnings structure, and rest is the expansion for
; the statements that come after this when statement in the current block.  We
; are to write the MV code for this when statement.

   (declare (xargs :guard (and (seq-when-p x)
                               (seq-name-p stream)
                               (seq-name-p warnings))))

   (let* ((condition         (second x))
          (subblock          (cddr x))
          (ends-with-returnp (seq-list-ends-with-returnp subblock))
          (bound-in-subblock (seq-block-names subblock nil)))

     (cond

; Easy case 1.  The subblock ends with a return, so we always either process it
; or rest but never both.

      (ends-with-returnp
       `(if ,condition
            ,(seqw-process-block subblock stream warnings nil)
          ,rest))


; Easy case 2.  The subblock doesn't end with a return, so we may process it or
; and rest; but since it binds no variables so the only thing that it changes is
; the stream.

      ((not bound-in-subblock)
       `(mv-let (!!!error !!!val ,stream ,warnings)
                (if ,condition
                    ,(seqw-process-block subblock stream warnings nil)
                  (mv nil nil ,stream ,warnings))
                (if !!!error
                    (mv !!!error !!!val ,stream ,warnings)
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
              (return-expansion  `(mv nil (list ,@bound-in-subblock) ,stream ,warnings))
              (new-subblock      (append subblock (list return-stmt)))
              (rebindings        (seq-make-let-pairs-for-when bound-in-subblock)))

         `(mv-let (!!!error !!!val ,stream ,warnings)
                  (if ,condition
                      ,(seqw-process-block new-subblock stream warnings nil)
                    ,return-expansion)
                  (if !!!error
                      (mv !!!error !!!val ,stream ,warnings)

; At this point, !!!val holds the list of all the values for the variables
; which were bound in the subblock.  We just need to redo these bindings so
; that they are available in rest.

                    (let* ,rebindings
                      (check-vars-not-free (!!!error !!!val) ,rest)))))))))

 (defun seqw-process-stmt (x stream warnings rest)
   (declare (xargs :guard (and (or (seq-bind-p x)
                                   (seq-when-p x)
                                   (seq-unless-p x)
                                   (seq-return-p x))
                               (seq-name-p stream)
                               (seq-name-p warnings))))
   (cond ((seq-bind-p x)
          (seqw-process-bind x stream warnings rest))
         ((seq-when-p x)
          (seqw-process-when x stream warnings rest))
         ((seq-unless-p x)
          (seqw-process-unless x stream warnings rest))
         (t
          (let ((type (first x))
                (value (second x)))
            (cond ((eq type 'return)
                   `(mv nil ,value ,stream ,warnings))
                  ((eq type 'return-raw)
                   value))))))

 (defun seqw-process-block (x stream warnings toplevelp)
   (declare (xargs :guard (and (seq-block-p x toplevelp)
                               (seq-name-p stream)
                               (seq-name-p warnings))))
   (if (atom (cdr x))
       (seqw-process-stmt (car x) stream warnings `(mv nil nil ,stream ,warnings))
     (let ((rest (seqw-process-block (cdr x) stream warnings toplevelp)))
       (seqw-process-stmt (car x) stream warnings rest)))))

(defun seqw-fn (stream warnings block)
  (declare (xargs :guard (and (seq-name-p stream)
                              (seq-name-p warnings)
                              (seq-block-p block t))))
  (let* ((names            (seq-block-names block t))
         (initial-bindings (seq-make-initial-let-pairs (remove-duplicates names))))
    `(let ,initial-bindings
       (declare (ignorable ,@names))
       ,(seqw-process-block block stream warnings t))))

(defmacro seqw (stream warnings &rest block)
  (seqw-fn stream warnings block))





(defun seqw-backtrack-fn (stream warnings blocks)
  (declare (xargs :guard (and (seq-name-p stream)
                              (seq-name-p warnings)
                              (seq-block-list-p blocks t)
                              (consp blocks))))
  (if (atom (cdr blocks))
      `(seqw ,stream ,warnings . ,(car blocks))
    `(mv-let (!!!error !!!val updated-stream updated-warnings)
             (seqw ,stream ,warnings . ,(car blocks))
             (if (not !!!error)
                 (mv !!!error !!!val updated-stream updated-warnings)
               (check-vars-not-free (!!!error !!!val)
                                    ,(seqw-backtrack-fn stream warnings (cdr blocks)))))))

(defmacro seqw-backtrack (stream warnings &rest blocks)
  (seqw-backtrack-fn stream warnings blocks))

