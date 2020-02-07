; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(program)

(defun cmds-back-to-boot-strap (wrld acc)

; We accumulate into acc the commands back to, but not including the boot-strap
; world.  At the top level, acc is nil and we return the list of commands since
; the boot-strap, in order.

  (declare (xargs :guard (plist-worldp wrld)))
  (cond ((endp wrld) ; impossible if we started with a post-boot-strap world
         acc)
        ((and (eq (caar wrld) 'command-landmark)
              (eq (cadar wrld) 'global-value))
         (let ((cmd (access-command-tuple-form (cddar wrld))))
           (cond ((and (consp cmd)
                       (member-eq (car cmd) '(exit-boot-strap-mode
                                              reset-prehistory)))
                  acc)
                 (t (cmds-back-to-boot-strap (cdr wrld) (cons cmd acc))))))
        (t (cmds-back-to-boot-strap (cdr wrld) acc))))

(defconst *keeper-cmds*
  '(defpkg include-book xdoc add-include-book-dir add-include-book-dir!))

(defun initial-keeper-cmds-length (cmds keeper-cmds acc)
  (cond ((endp cmds) acc)
        (t (let* ((cmd0 (car cmds))
                  (cmd (if (and (consp cmd0)
                                (eq (car cmd0) 'local))
                           (cadr cmd0)
                         cmd0))
                  (keeper-p (and (consp cmd)
                                 (member-eq (car cmd) keeper-cmds))))
             (cond (keeper-p (initial-keeper-cmds-length (cdr cmds)
                                                         keeper-cmds
                                                         (1+ acc)))
                   (t acc))))))

(defun ubi-fn (args state)
  (declare (xargs :guard (symbol-listp args) :stobjs state))
  (let* ((wrld (w state))
         (cmds (cmds-back-to-boot-strap wrld nil))
         (keeper-cmds (union-eq args *keeper-cmds*))
         (len-cmds (length cmds))
         (len-keeper-cmds
          (initial-keeper-cmds-length cmds keeper-cmds 0)))
    (cond ((eql len-cmds len-keeper-cmds)
           (pprogn (fms "There is nothing to undo, since all commands after ~
                         the boot-strap are ~v0 commands.~|"
                        (list (cons #\0 keeper-cmds))
                        *standard-co* state nil)
                   (value :invisible)))
          (t (ubu len-keeper-cmds)))))

(defmacro ubi (&rest args)
  (declare (xargs :guard (symbol-listp args)))
  `(ubi-fn ',args state))

(defxdoc ubi
  :parents (kestrel-utilities history)
  :short "Undo back up to longest initial segment containing only calls of
 certain symbols, including @(tsee defpkg) and @(tsee include-book)."
  :long "<p>The following example explains how @(':ubi') works.  We start up
 ACL2 and submit the following @(see command)s.</p>

 @({
 (include-book \"kestrel/utilities/ubi\" :dir :system)
 (local (include-book \"kestrel/utilities/system/world-queries\" :dir :system))
 (defpkg \"FOO\" nil)
 (include-book \"kestrel/std/system/defun-sk-queries\" :dir :system))
 (defun f (x) x)
 (include-book \"arithmetic/top\" :dir :system)
 (defun g (x) x)
 })

 <p>We can use @(':')@(tsee pbt) to see where we are:</p>

 @({
 ACL2 !>:pbt 0
            0  (EXIT-BOOT-STRAP-MODE)
    d       1  (INCLUDE-BOOK \"kestrel/utilities/ubi\"
                             :DIR ...)
    d       2  (LOCAL (INCLUDE-BOOK \"kestrel/utilities/system/world-queries\"
                                    :DIR ...))
            3  (DEFPKG \"FOO\" NIL)
    d       4  (INCLUDE-BOOK \"kestrel/std/system/defun-sk-queries\"
                             :DIR ...)
  L         5  (DEFUN F (X) ...)
    d       6  (INCLUDE-BOOK \"arithmetic/top\" :DIR ...)
  L         7:x(DEFUN G (X) ...)
 ACL2 !>
 })

 <p>The @(':ubi') command, which could be viewed as abbreviating ``Undo Back to
 Initial commands that we want to keep,'' undoes commands to keep the longest
 initial segment of commands in the list @('*keeper-cmds*'), including @(tsee
 include-book), @(tsee defpkg), and @(tsee xdoc) commands; any such command may
 be @(tsee local).  (Such commands are typically those that set things up for
 the rest of the @(see events) in a given book; an @(tsee xdoc) command may be
 laid down when printing documentation at the terminal.)</p>

 <p>So to continue the example above:</p>

 @({
 ACL2 !>:ubi
    d       4:x(INCLUDE-BOOK \"kestrel/std/system/defun-sk-queries\"
                             :DIR ...)
 ACL2 !>:pbt 0
            0  (EXIT-BOOT-STRAP-MODE)
    d       1  (INCLUDE-BOOK \"kestrel/utilities/ubi\"
                             :DIR ...)
    d       2  (LOCAL (INCLUDE-BOOK \"kestrel/utilities/system/world-queries\"
                                    :DIR ...))
            3  (DEFPKG \"FOO\" NIL)
    d       4:x(INCLUDE-BOOK \"kestrel/std/system/defun-sk-queries\"
                             :DIR ...)
 ACL2 !>
 })

 <p>Note that when successful, @(':ubi') generates a call of @(tsee ubu), which
 in turn prints out the most recent remaining command (in this case, command
 number 4).  But @(':ubi') can fail if there is no undoing to do: we can extend
 the log above by trying to run @(':ubi') again.</p>

 @({
 ACL2 !>:ubi

 There is nothing to undo, since all commands after the boot-strap are
 DEFUN, DEFPKG, INCLUDE-BOOK, XDOC, ADD-INCLUDE-BOOK-DIR or
 ADD-INCLUDE-BOOK-DIR! commands.
 ACL2 !>
 })

 <p>Note that @(':ubi') only looks at commands after the latest command that is
 a call of @(tsee reset-prehistory), if any.  Continuing the example above,
 where the final command is number 4 as shown above, let us execute these
 commands.</p>

 @({
 (defun f (x) x)
 (reset-prehistory)
 (include-book \"arithmetic/top\" :dir :system)
 (defun g (x) x)
 })

 <p>Here is a subsequent log.  Notice that @(':ubi') only considers what is
 after the call of @(tsee reset-prehistory).  Thus, the initial segment that we
 keep concludes with the @('include-book') that is command number 1, because
 @(tsee defun) of @('f') preceding that command is irrelevant (since that
 @('defun') precedes the @('reset-prehistory') call).</p>

 @({
 ACL2 !>:pbt 0
            0  (RESET-PREHISTORY)
    d       1  (INCLUDE-BOOK \"arithmetic/top\" :DIR ...)
  L         2:x(DEFUN G (X) ...)
 ACL2 !>:ubi
    d       1:x(INCLUDE-BOOK \"arithmetic/top\" :DIR ...)
 ACL2 !>
 })

 <p>Finally, note that @('ubi') can be given any number of symbol arguments.
 These are added to @('*keeper-commands*') as those whose calls may appear in
 the initial segment of post-boot-strap commands that remain after undoing.
 Consider for example this @(see world):</p>

 @({
 ACL2 !>:pbt 0
            0  (EXIT-BOOT-STRAP-MODE)
    d       1  (INCLUDE-BOOK \"kestrel/utilities/ubi\"
                             :DIR ...)
    d       2  (LOCAL (INCLUDE-BOOK \"kestrel/utilities/system/world-queries\"
                                    :DIR ...))
            3  (DEFPKG \"FOO\" NIL)
    d       4  (INCLUDE-BOOK \"kestrel/std/system/defun-sk-queries\"
                             :DIR ...)
  L         5  (DEFUN F (X) ...)
    d       6  (INCLUDE-BOOK \"arithmetic/top\" :DIR ...)
  L         7:x(DEFUN G (X) ...)
 ACL2 !>
 })

 <p>Our first example above showed that submitting @(':ubi') leaves us with
 four commands after the boot-strap world.  Note that submitting @(':ubi') is
 equivalent to submitting @('(ubi)'); see @(see keyword-commands).  Suppose
 that instead, we submit the command @('(ubt defun)').  Then commands that are
 @('defun') calls are allowed to remain in the resulting world.  In this
 example, every command is either a call of @('defun') or a call of one of the
 default commands in @('*keeper-commands*'), so @('(ubi defun)') has no effect.
 If we then execute some other sort of command, say a call of @(tsee defmacro),
 then @('(ubi defun)') will undo it, leaving us with the seven commands
 displayed above.  Of course, @('(ubi defun defmacro)') would not undo the
 @('defmacro') call.</p>")
