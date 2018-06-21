;; AUTHORS:
;; Shilpi Goel <shigoel@cs.utexas.edu>
;; Soumava Ghosh <soumava@cs.utexas.edu>
;; Matt Kaufmann <kaufmann@cs.utexas.edu>

(in-package "X86ISA")

(include-book "syscall-numbers")
(include-book "environment" :ttags (:undef-flg))

(local (include-book "std/lists/nthcdr" :dir :system))

(local (include-book "std/lists/take" :dir :system))

;; ======================================================================

(defsection syscalls
  :parents (machine)
  :short "Extending the x86 ISA with the system call model in the
  application-level view"

  :long "<p>System calls are non-deterministic --- different runs of a
program with syscalls can yield different results on the same machine.
Since our ACL2-based x86 specification serves both as an executable
simulator and a formal model to do x86 code proofs, we need to be able
to do the following:</p>

<ol>
<li>  Simulate a run of a program with syscalls on concrete data </li>
<li>  Reason about such a program </li>
</ol>

<p>Ideally, to serve both these tasks, we would model enough features
of the x86 to simulate an operating system running on it; the syscall
service can then be provided by this simulated OS.  However, since
loading a serious OS on our formal model is more than non-trivial, we
chose to do this task differently.</p>

<p>For simulations, we set up our x86 model to use the results
returned by some raw Lisp functions that invoke the syscalls by
interacting directly with the underlying operating system.  More
precisely, we install alternate raw Lisp definitions for some
functions, using trust tags.  Thus, simulation of all instructions
except syscalls happens within ACL2 but for syscalls, we escape out of
Lisp \(and hence, ACL2\) to get the \"real\" results.  However, these
raw Lisp functions are not really functions in the logical sense since
they can return different values for the same input arguments.  So we
need a logical story that justifies this setup for simulations.  To
this end, we define an oracle field in the x86 state that holds all
the results of syscalls starting with that state.  Whenever we want to
see the effects of a syscall in logic, we simply consult this
oracle.</p>

<p>It is important that our setup prohibits proofs of theorems that
say that some syscall returns a specific value.  If that were the
case, then due to the non-determinism inherent in syscalls, we might
be able to prove that the same syscall returns some other value in
some other ACL2 session.  That could allow us to certify books with
contradictory theorems, and then include them both to prove nil.  Or
perhaps worse yet, we could prove an instance of <tt>\(not \(equal x
x\)\)</tt> by instantiating x with a term that invokes syscall!  The
only reasoning about syscall that our setup should allow must be based
on results that are specified by the oracle field.  As discussed
below, we make this happen by arranging for the oracle field to be
completely hidden during evaluation in the top-level loop, where raw
Lisp functions are applied to implement syscall; but during reasoning,
the raw Lisp functions are \"taken out\" of the model.</p>

<p>At a high level, the following three properties hold for our
setup:</p>

<ul>

<li> <b>\(L\)</b> Our official x86 model consists of ordinary logic
definitions, without the use of a trust tag.</li>

<li> <b>\(E\)</b> An execution environment, which requires a trust tag,
    can allow us to run the model using raw Lisp functions that
    directly interact with the underlying OS to provide the syscall
    service.</li>

<li> <b>\(C\)</b> The following connection exists between the logical
    model and the execution environment.  Let @('x0') be an x86
    state. Suppose in our execution environment, the evaluation of
    <tt>\(x86-run x0\)</tt> returns @('x1') and generates a syscall
    trace @('TR'). Then, the following is true for our logical model:
    if the oracle of x86 extends @('TR') and the other fields of x86
    are those of @('x0'), then <tt>\(x86-run x0\) = x1</tt>.  Note
    that all bets are off if the oracle does not extend @('TR')
    appropriately.</li>

</ul>

<p>Note that because of \(C\), we know that evaluation results
produced with raw Lisp functions installed will not be contradicted by
theorems proved later; in fact, each evaluation produces a theorem
under a suitable extra hypothesis about the oracle.</p>

<p>Here are some details about our implementation, where \"top-level
  evaluation\" and \"during reasoning\", also known as \"impure\" and
  \"pure\" evaluation \(respectively\), partition evaluation into that
  done outside or inside the prover \(or proof-builder\),
  respectively.  Below, we use \"attach\" in quotes to refer to
  changing a definition.  In our case we probably will avoid
  defattach, in part at least to avoid complicating the defattach
  story, but also to give us the freedom to \"attach\" to a function
  introduced by defun as opposed to encapsulate.</p>

<ol>

<li><p>During top-level evaluation, calling of oracle accessor and
   updater functions will generate an error.</p>

   <p>We ensure this by construction.  We \"attach\" the raw Lisp
   syscall functions \(which do not access/update the oracle field but
   interact with the underlying OS directly to get the results of
   executing a syscall\) to the logic definitions of the syscall
   functions, thereby bypassing the oracle during execution.
   Moreover, all the oracle accessor and updater functions and macros
   are either untouchable \(the primitive macros that come with the
   stobj definition --- env and !env\) or cause an error upon
   execution \(\"safe\" functions --- env-read and
   pop-x86-oracle\).</p>

   <p>Note that functions to be smashed should be declared notinline.
   That way we can be confident that the compiler will not inline the
   function definitions for efficiency \(and \"smashing\" inlined
   functions is not possible\).</p></li>

<li> <p>During proofs, raw Lisp functions cannot be called.</p>

   <p>We smash with definitions that avoid calling raw Lisp code when
   state globals @('in-prove-flg') or @('in-verify-flg') are set.</p>

   <p>If, in the future, we wind up using @(':program') mode functions
   for any of this work that need not to become @(':logic') mode
   functions, especially without guards verified \(hence executing in
   the logic\), we can further disallow the user from bringing these
   raw Lisp functions into the ACL2 logic by using
   @('program-fns-with-raw-code') to declare these functions as
   \"special\".</p></li>

</ol>

<p> For more details, please refer to the following paper: </p>

<p>Shilpi Goel, Warren A. Hunt, Jr., Matt Kaufmann, and Soumava
Ghosh. <em>Simulation and Formal Verification of x86 Machine-Code
Programs that make System Calls.</em> In Formal Methods in
Computer-Aided Design (FMCAD), 2014.</p>

<p>The logic definitions of syscalls might be incomplete.  For
example, we don't model all the errors yet; we don't have a global
error variable that's updated when an error occurs; we don't keep
track of the maximum allowed object offset, etc.  We plan to make this
specification more and more complete as time goes on.  Of course,
anything we don't want to implement can always be thought of or
implemented as something obtained from the oracle, which might be a
really good thing to do to keep the model simple.</p>"
  )

;; ======================================================================

;; I'm modeling only the following oflags for now (from
;; /usr/include/asm-generic/fcntl.h):

(defconst *O_RDONLY*	#x00000000) ;;  open for reading only
(defconst *O_WRONLY*	#x00000001) ;;  open for writing only
(defconst *O_RDWR*      #x00000002) ;;  open for reading and writing
(defconst *O_CREAT*	#x00000100) ;;  create file if it does not exist
(defconst *O_EXCL*      #x00000200) ;;  error if O_CREAT and file exists
(defconst *O_TRUNC*	#x00001000) ;;  truncate size to 0
(defconst *O_APPEND*	#x00002000) ;;  append on each write

;; I'm not going to worry about mode (which I'll probably call
;; :permissions in the future) right now.

;; Important notes about oflags: (mostly lifted from Linux "man 2
;; open").

;; 1.  The argument flags must include one of the following access
;;     modes: O_RDONLY, O_WRONLY, or O_RDWR.  These request opening
;;     the file read-only, write-only, or read/write, respectively.
;;     In addition, zero or more file creation flags and file status
;;     flags can be bitwise-or'd in flags.  The file creation flags
;;     are O_CREAT, O_EXCL, O_NOCTTY, and O_TRUNC.  The distinction
;;     between these two groups of flags is that the file status flags
;;     can be retrieved and (in some cases) modified using fcntl(2).

;; 2.  Unlike the other values that can be specified in flags, the
;;     access mode values O_RDONLY, O_WRONLY, and O_RDWR, do not
;;     specify individual bits.  Rather, they define the low order two
;;     bits of flags, and are defined respectively as 0, 1, and 2.  In
;;     other words, the combination O_RDONLY | O_WRONLY is a logical
;;     error, and certainly does not have the same meaning as O_RDWR.
;;     Linux reserves the special, nonstandard access mode 3 (binary
;;     11) in flags to mean: check for read and write permission on
;;     the file and return a descriptor that can't be used for reading
;;     or writing.  This nonstandard access mode is used by some Linux
;;     drivers to return a descriptor that is only to be used for
;;     device-specific ioctl(2) operations.

;; 3.  The (undefined) effect of O_RDONLY | O_TRUNC varies among
;;     implementations.  On many systems the file is actually
;;     truncated.

;; Remember that no file offset is associated with files that do not
;; support seeking (i.e., terminals).  Such files always read from the
;; current position.  The value of a file offset associated with such
;; a file is undefined --- I'll take that as zero.

(defn file-descriptor-fieldp (fd)

  ;; In the future, I will add a :permissions field to store the mode
  ;; when syscall open is called with flag O_CREAT.

  (and (alistp fd)
       (consp (assoc :name fd))
       (stringp (cdr (assoc :name fd)))
       (consp (assoc :offset fd))
       (natp (cdr (assoc :offset fd)))
       (consp (assoc :mode fd))
       (natp (cdr (assoc :mode fd)))))

(defn file-contents-fieldp (c)
  (and (alistp c)
       (consp (assoc :contents c))
       (stringp (cdr (assoc :contents c)))))

(define grab-bytes (lst)
  :guard (true-listp lst)
  :returns (lst byte-listp :hyp (force (true-listp lst)))
  (if (endp lst)
      nil
    (if (n08p (car lst))
        (cons (car lst) (grab-bytes (cdr lst)))
      nil)))

(define coerce-bytes (lst)
  :guard (true-listp lst)
  (if (endp lst)
      nil
    (cons (n08 (nfix (car lst))) (coerce-bytes (cdr lst))))
  ///

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm byte-listp-coerce-bytes
    (implies (force (true-listp lst))
             (byte-listp (coerce-bytes lst)))
    :rule-classes :type-prescription))

;; ======================================================================

(defsection syscalls-logic
  :parents (syscalls)
  :short "Logical definitions for syscalls to be used in the
  application-level view for reasoning"

  :long "<p>All the <tt>*-logic</tt> functions (like @(see
  syscall-read-logic)) should be untouchable (@(see push-untouchable))
  --- we want to disallow the use of these functions during evaluation
  as well as proof since they aren't the top-level interface
  functions (like @(see syscall-read)).</p>"

  (local (xdoc::set-default-parents syscalls-logic))

  (define syscall-read-logic (fd *buf count x86)

    :guard (and (integerp fd)
                (integerp *buf)
                (natp count))

    :long "<p>From the read(2) man page (Linux):</p>

    <p><tt>read()</tt> attempts to read up to <tt>count</tt> bytes
    from file descriptor <tt>fd</tt> into the buffer starting at
    <tt>buf</tt>.</p>

    <p>If count is zero, <tt>read()</tt> returns zero and has no other
    results.  If count is greater than <tt>SSIZE_MAX</tt>, the result
    is unspecified.</p>

    <p>RETURN VALUE</p>

   <p>On success, the number of bytes read is returned (zero indicates
    end of file), and the file position is advanced by this number.
    It is not an error if this number is smaller than the number of
    bytes requested; this may happen for example because fewer bytes
    are actually available right now (maybe because we were close to
    end-of-file, or because we are reading from a pipe, or from a
    terminal), or because @('read()') was interrupted by a signal.  On
    error, -1 is returned, and errno is set appropriately.  In this
    case it is left unspecified whether the file position (if any)
    changes.</p>"

    (declare (ignorable fd *buf count x86))

    (b* (
         ;; Get the name and offset of the object using fd, the file
         ;; descriptor:
         (obj-fd-field (read-x86-file-des fd x86))
         ((when (not (file-descriptor-fieldp obj-fd-field)))
          ;; If the books were not built with X86ISA_EXEC = t, the
          ;; execution will stop here.  I don't need to display this
          ;; error message elsewhere in this function.
          (b* ((- (cw "~%Error: File Descriptor Field ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Descriptor Field ill-formed. Maybe these books were built
with X86ISA_EXEC set to nil? See :doc x86isa-build-instructions."
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         (obj-name (cdr (assoc :name obj-fd-field)))
         (obj-offset (cdr (assoc :offset obj-fd-field)))
         (obj-mode (cdr (assoc :mode obj-fd-field)))
         ;; TO-DO@Shilpi:
         ;; For now, I'm ignoring errors/behaviors that occur if other
         ;; flags are present.  However, if the file doesn't exist,
         ;; file-contents-fieldp will raise an error.
         ((when (and (not (equal (logand #b11 obj-mode) *O_RDONLY*))
                     (not (equal (logand #b11 obj-mode) *O_RDWR*))))
          (b*
           ((- (cw "~%Error: File has not been opened in the read access mode..~%~%")))
           (mv -1 x86)))

         ;; Get the contents field of the object name:
         (obj-contents-field (read-x86-file-contents obj-name x86))
         ((when (not (file-contents-fieldp obj-contents-field)))
          (b* ((- (cw "~%Error: File Contents Field ill-formed.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Contents Field ill-formed."
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         (obj-contents (cdr (assoc :contents obj-contents-field)))

         ;; Get count bytes of obj-contents from the obj-offset: Note
         ;; that obj-offset should be zero for non-seeking objects like
         ;; the terminal.
         (bytes-of-obj (string-to-bytes obj-contents))

         ((when (< (len bytes-of-obj) obj-offset))
          ;; (= (len bytes-of-obj) obj-offset) when EOF is reached.
          (b* ((- (cw "~%Error: Offset is beyond the size of the object.~%~%")))
              (mv -1 x86)))

         (bytes-of-obj-from-offset (nthcdr obj-offset bytes-of-obj))
         (count-bytes-of-obj-from-offset
          (if (eql bytes-of-obj-from-offset nil)
              nil ;; EOF reached.
            (take count bytes-of-obj-from-offset)))
         (only-bytes-of-obj-from-offset
          (grab-bytes count-bytes-of-obj-from-offset))

         (n (if (eql only-bytes-of-obj-from-offset nil)
                0 ;; EOF reached.
              (len only-bytes-of-obj-from-offset)))

         ;; Update the environment:

         ;; Write the read bytes to the buffer pointed to by *buf (but
         ;; only if only-bytes-of-obj-from-offset is not nil):

         ((mv flg x86)
          (if (equal only-bytes-of-obj-from-offset nil)
              (mv nil x86)
            (if (and (canonical-address-p *buf)
                     (canonical-address-p (+ (len only-bytes-of-obj-from-offset) *buf)))
                (write-bytes-to-memory
                 *buf only-bytes-of-obj-from-offset x86)
              (mv t x86))))
         ((when flg)
          (b* ((- (cw "~%Error: Buffer Memory Error.~%~%")))
              (mv -1 x86)))

         ;; Update the file offset of the object:
         (x86 (write-x86-file-des fd
                                  (put-assoc
                                   :offset
                                   (+ n obj-offset)
                                   obj-fd-field) x86)))
        (mv n x86)))

  (define syscall-read (fd *buf count x86)
    :inline nil
    :guard (and (integerp fd)
                (integerp *buf)
                (natp count))
    (declare (ignorable fd *buf count x86))
    (syscall-read-logic fd *buf count x86)

    ///

    (local (in-theory (e/d (syscall-read-logic) ())))

    (defthm integerp-mv-nth-0-syscall-read
      (integerp (mv-nth 0 (syscall-read fd *buf count x86)))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-1-syscall-read
      (implies (and (x86p x86)
                    (integerp fd))
               (x86p (mv-nth 1 (syscall-read fd *buf count x86))))))

  (define syscall-write-logic (fd *buf count x86)
    :guard (and (integerp fd)
                (integerp *buf)
                (natp count))

    :long "<p>From the write(2) man page (Linux):</p>

    <p>@('write()') writes up to <tt>count</tt> bytes from the buffer
    pointed <tt>buf</tt> to the file referred to by the file
    descriptor <tt>fd</tt>.</p>

    <p>The number of bytes written may be less than count if, for
    example, there is insufficient space on the underlying physical
    medium, or the <tt>RLIMIT_FSIZE</tt> resource limit is
    encountered (see @('setrlimit(2)')), or the call was interrupted
    by a signal handler after having written less than count
    bytes.  (See also @('pipe(7)').)</p>

    <p>For a seekable file (i.e., one to which @('lseek(2)') may be
    applied, for example, a regular file) writing takes place at the
    current file offset, and the file offset is incremented by the
    number of bytes actually written.  If the file was @('open(2)')ed
    with <tt>O_APPEND</tt>, the file offset is first set to the end of
    the file before writing.  The adjustment of the file offset and
    the write operation are performed as an atomic step.</p>

    <p>RETURN VALUE</p>
    <p>On success, the number of bytes written is returned (zero
    indicates nothing was written).  On error, -1 is returned, and
    errno is set appropriately.</p>

    <p>If count is zero and fd refers to a regular file, then
    @('write()') may return a failure status if one of the errors
    below is detected.  If no errors are detected, 0 will be returned
    without causing any other effect.  If count is zero and fd refers
    to a file other than a regular file, the results are not
    specified.</p>"

    (declare (ignorable fd *buf count x86))

    (b* (
         ;; Get count bytes from *buf.
         ((mv flg count-bytes-from-buffer x86)
          (if (and (canonical-address-p *buf)
                   (canonical-address-p (+ count *buf)))
              (read-bytes-from-memory *buf count x86 nil)
            (mv t 0 x86)))
         ((when flg)
          (b* ((- (cw "~%Error: Buffer Memory Error.~%~%")))
              (mv -1 x86)))

         ;; Get the name and offset of the object using fd, the file
         ;; descriptor:
         (obj-fd-field (read-x86-file-des fd x86))
         ;; If the books were not built with X86ISA_EXEC = t, the
         ;; execution will stop here.  I don't need to display this
         ;; error message elsewhere in this function.
         ((when (not (file-descriptor-fieldp obj-fd-field)))
          (b* ((- (cw "~%Error: File Descriptor Field ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Descriptor Field ill-formed. Maybe these books were
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions."
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         (obj-name (cdr (assoc :name obj-fd-field)))
         (obj-offset (cdr (assoc :offset obj-fd-field)))
         (obj-mode (cdr (assoc :mode obj-fd-field)))
         ((when (and (not (equal (logand #b11 obj-mode) *O_WRONLY*))
                     (not (equal (logand #b11 obj-mode) *O_RDWR*))))
          (b*
           ((- (cw "~%Error: File has not been opened in the write access mode.~%~%")))
           (mv -1 x86)))

         ;; Get the contents field of the object name:
         (obj-contents-field (read-x86-file-contents obj-name x86))
         ((when (not (file-contents-fieldp obj-contents-field)))
          (b* ((- (cw "~%Error: File Contents Field ill-formed.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Contents Field ill-formed"
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         (obj-contents (cdr (assoc :contents obj-contents-field)))

         (bytes-of-obj (string-to-bytes obj-contents))

         ;; Move the offset to the end of the file if O_APPEND flag was
         ;; used to open the file.
         (obj-offset (if (equal (logand *O_APPEND* obj-mode) *O_APPEND*)
                         (len bytes-of-obj)
                       obj-offset))

         (bytes-of-obj-till-offset
          ;; Coerce-Bytes takes care of inserting zeroes when obj-offset
          ;; is larger than obj-len.
          (coerce-bytes (take obj-offset bytes-of-obj)))
         (new-byte-contents (append bytes-of-obj-till-offset
                                    count-bytes-from-buffer))
         (new-string-contents (coerce (bytes-to-charlist
                                       new-byte-contents) 'STRING))

         ;; Update the environment:

         ;; Write the bytes read from the buffer to the file pointed to by fd:

         (x86 (write-x86-file-contents
               obj-name
               (put-assoc :contents new-string-contents
                          obj-contents-field)
               x86))

         ;; Update the file offset.

         (x86 (write-x86-file-des
               fd
               (put-assoc
                :offset (+ count obj-offset) obj-fd-field) x86)))
        (mv count x86)))

  (define syscall-write (fd *buf count x86)
    :inline nil
    :guard (and (integerp fd)
                (integerp *buf)
                (natp count))
    (declare (ignorable fd *buf count x86))
    (syscall-write-logic fd *buf count x86)

    ///

    (local (in-theory (e/d (syscall-write-logic) ())))

    (defthm integerp-mv-nth-0-syscall-write
      (implies (natp count)
               (integerp (mv-nth 0 (syscall-write fd *buf count x86))))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-1-syscall-write
      (implies (and (x86p x86)
                    (integerp fd))
               (x86p (mv-nth 1 (syscall-write fd *buf count x86))))))

  (define syscall-open-logic (pathname oflags mode x86)

    :long "<p>From the @('open(2)') man page (Linux):</p>

    <p>Given a pathname for a file, @('open()') returns a file
    descriptor, a small, nonnegative integer for use in subsequent
    system calls
    (@('read(2)'), @('write(2)'), @('lseek(2)'), @('fcntl(2)'), etc.).
    The file descriptor returned by a successful call will be the
    lowest-numbered file descriptor not currently open for the
    process.</p>

    <p>The file offset is set to the beginning of the file (see
    @('lseek(2)')).</p>

    <p>The argument flags must include one of the following access
    modes: <tt>O_RDONLY</tt>, <tt>O_WRONLY</tt>, or <tt>O_RDWR</tt>.
    These request opening the file read- only, write-only, or
    read/write, respectively.</p>

    <p>In addition, zero or more file creation flags and file status
    flags can be bitwise-or'd in flags.  The file creation flags are
    <tt>O_CREAT</tt>, <tt>O_EXCL</tt>, <tt>O_NOCTTY</tt>, and
    <tt>O_TRUNC</tt>.</p>"

    :guard (and (stringp pathname)
                (natp oflags)
                (natp mode))

    (declare (ignorable pathname oflags mode x86))

    (b* (
         ;; I'm obtaining the new-fd from the oracle.  I could have
         ;; have computed it myself as well since the man page for
         ;; open(2) says the following:

         ;; "The file descriptor returned by a successful call will be
         ;; the lowest-numbered file descriptor not currently open for
         ;; the process."

         ((mv new-fd x86)
          (pop-x86-oracle x86))
         ;; If the books were not built with X86ISA_EXEC = t, the
         ;; execution will stop here.  I don't need to display this
         ;; error message elsewhere in this function.
         ((when (not (natp new-fd)))
          (b* ((- (cw "~%Error: File Descriptor ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Descriptor ill-formed. Maybe these books were
not built with X86ISA_EXEC set to t? See :doc x86sa-build-instructions."
                               (ms x86))
                         x86)))
              (mv -1 x86)))

         ((when (and (not (equal (logand #b11 mode) *O_RDONLY*))
                     (not (equal (logand #b11 mode) *O_WRONLY*))
                     (not (equal (logand #b11 mode) *O_RDWR*))))
          (b*
           ((- (cw "~%Error: File mode is not an appropriate access mode.~%~%")))
           (mv -1 x86)))

         (obj-fd-field (read-x86-file-des new-fd x86))
         (obj-contents-field (read-x86-file-contents pathname x86))

         ((mv flg obj-contents-field x86)
          (if (equal (logand *O_CREAT* mode) *O_CREAT*)
              (if (and ;; File exists.
                   (file-descriptor-fieldp obj-fd-field)
                   (file-contents-fieldp obj-contents-field))

                  (if (equal (logand *O_EXCL* mode) *O_EXCL*)
                      (mv t obj-contents-field x86)
                    (mv nil obj-contents-field x86))

                ;; File doesn't exist: create an empty file.
                (b* ((x86 (write-x86-file-contents
                           pathname
                           (acons :contents "" nil) x86))
                     (- (cw "here 0")))
                    (mv nil (acons :contents "" nil) x86)))
            (mv nil obj-contents-field x86)))

         ((when flg)
          (b*
           ((- (cw "~%Error: [O_EXCL Mode] O_CREAT used but file already exists.~%~%")))
           (mv -1 x86)))

         (x86
          (if (and (equal (logand *O_TRUNC* mode) *O_TRUNC*)
                   (file-descriptor-fieldp obj-fd-field)
                   (file-contents-fieldp obj-contents-field))
              ;; Truncate the existing file.
              (write-x86-file-contents pathname
                                       (acons :contents "" nil) x86)
            x86))

         (x86 (if (equal obj-contents-field nil)
                  (write-x86-file-contents pathname
                                           (acons :contents "" nil) x86)
                x86))

         (fd-field
          ;; The file offset is set to the beginning of the file.
          (put-assoc :name pathname
                     (put-assoc :offset 0
                                (put-assoc :mode oflags
                                           (put-assoc :permissions
                                                      mode nil)))))

         (x86 (write-x86-file-des new-fd fd-field x86)))
        (mv new-fd x86)))

  (define syscall-open (pathname oflags mode x86)
    :inline nil
    :guard (and (stringp pathname)
                (natp oflags)
                (natp mode))
    (declare (ignorable pathname oflags mode x86))
    (syscall-open-logic pathname oflags mode x86)

    ///

    (local (in-theory (e/d (syscall-open-logic) ())))

    (defthm integerp-mv-nth-0-syscall-open
      (implies (and (x86p x86)
                    (stringp pathname))
               (integerp (mv-nth 0 (syscall-open pathname oflags mode x86))))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-1-syscall-open
      (implies (and (x86p x86)
                    (stringp pathname))
               (x86p (mv-nth 1 (syscall-open pathname oflags mode x86))))))

  (define syscall-close-logic (fd x86)

    :guard (integerp fd)
    :long "<p>From the @('close(2)') man page (Linux):</p>

    <p>@('close()') closes a file descriptor, so that it no longer
    refers to any file and may be reused.</p>

    <p>RETURN VALUES</p>
    <p>@('close()') returns zero on success.  On error, -1 is
    returned, and @('errno') is set appropriately.</p>"

    (declare (ignorable fd x86))

    (b* ((obj-fd-field (read-x86-file-des fd x86))
         ((when (not (file-descriptor-fieldp obj-fd-field)))
          (b* ((- (cw "~%Error: File Descriptor Field ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Descriptor Field ill-formed. Maybe these books were
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions."
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         (x86 (delete-x86-file-des fd x86)))
        (mv 0 x86)))

  (define syscall-close (fd x86)
    :inline nil
    :guard (integerp fd)
    (declare (ignorable fd x86))
    (syscall-close-logic fd x86)

    ///

    (local (in-theory (e/d (syscall-close-logic) ())))

    (defthm integerp-mv-nth-0-syscall-close
      (integerp (mv-nth 0 (syscall-close fd x86)))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-1-syscall-close
      (implies (and (x86p x86)
                    (integerp fd))
               (x86p (mv-nth 1 (syscall-close fd x86))))))

  (define syscall-lseek-logic (fd offset whence x86)

    :long "<p>From the @('lseek(2)') man page (Linux):</p>

    <p>The @('lseek()') function repositions the offset of the open
    file associated with the file descriptor fd to the argument offset
    according to the directive whence as follows:</p>

    <p><tt>SEEK_SET</tt> The offset is set to offset bytes.</p>

    <p><tt>SEEK_CUR</tt> The offset is set to its current location
    plus offset bytes.</p>

    <p><tt>SEEK_END</tt> The offset is set to the size of the file
    plus offset bytes.</p>

    <p>The @('lseek()') function allows the file offset to be set
    beyond the end of the file (but this does not change the size of
    the file).  If data is later written at this point, subsequent
    reads of the data in the gap (a \"hole\") return null bytes ('\0')
    until data is actually written into the gap.</p>

    <p>RETURN VALUE</p>
    <p>Upon successful completion, @('lseek()') returns the resulting
    offset location as measured in bytes from the beginning of the
    file.  On error, the value (<tt>off_t</tt>) -1 is returned and
    <tt>errno</tt> is set to indicate the error.</p>

    <p>NOTES</p>

    <p>When converting old code, substitute values for whence with the
    follow ing macros:</p>

    <p>old       new</p>
    <p>0        SEEK_SET</p>
    <p>1        SEEK_CUR</p>
    <p>2        SEEK_END</p>

    <p>TO-DO: I have not modeled @('SEEK_HOLE') and @('SEEK_DATA')
    \(available on Linux systems\).</p>"

    :guard (and (natp fd)
                (integerp offset)
                (natp whence))
    (declare (ignorable fd offset whence x86))

    (b* (
         ;; Get the name and offset of the object using fd, the file
         ;; descriptor:
         (obj-fd-field (read-x86-file-des fd x86))
         ((when (not (file-descriptor-fieldp obj-fd-field)))
          (b* ((- (cw "~%Error: File Descriptor Field ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Descriptor Field ill-formed. Maybe these books were
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions."
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         (obj-name (cdr (assoc :name obj-fd-field)))
         (obj-offset (cdr (assoc :offset obj-fd-field)))

         ;; Update the environment (the file offset):
         ((mv new-offset x86)
          (case whence
            (0 ;; SEEK_SET
             (b* (((when (not (natp offset)))
                   (b* ((- (cw "~%Error: SEEK_SET: New file offset not a Natp.~%~%")))
                       (mv -1 x86)))
                  (x86 (write-x86-file-des
                        fd
                        (put-assoc
                         :offset offset obj-fd-field) x86)))
                 (mv offset x86)))
            (1 ;; SEEK_CUR
             (b* (((when (not (natp (+ obj-offset offset))))
                   (b* ((- (cw "~%Error: SEEK_CUR: New file offset not a natp.~%~%")))
                       (mv -1 x86)))
                  (x86 (write-x86-file-des
                        fd
                        (put-assoc
                         :offset (+ obj-offset offset) obj-fd-field) x86)))
                 (mv (+ obj-offset offset) x86)))
            (2 ;; SEEK_END
             ;; Get the contents field of the object name:
             (b* ((obj-contents-field (read-x86-file-contents obj-name x86))
                  ((when (not (file-contents-fieldp obj-contents-field)))
                   (b* ((- (cw "~%Error: File Contents Field ill-formed.~%~%"))
                        (x86 (!ms (list (rip x86)
                                        "File Contents Field ill-formed"
                                        (ms x86))
                                  x86)))
                       (mv -1 x86)))
                  (obj-contents (cdr (assoc :contents obj-contents-field)))

                  (bytes-of-obj (string-to-bytes obj-contents))
                  (obj-len (len bytes-of-obj))
                  ((when (not (natp (+ obj-len offset))))
                   (b* ((- (cw "~%Error: SEEK_END: New file offset not a natp.~%~%")))
                       (mv -1 x86)))
                  (x86 (write-x86-file-des
                        fd
                        (put-assoc
                         :offset (+ obj-len offset) obj-fd-field) x86)))
                 (mv (+ obj-len offset) x86)))
            (t
             (b* ((- (cw "~%Error: Unsupported whence value.~%~%"))
                  (x86 (!ms (list (rip x86)
                                  "Unsupported whence value."
                                  (ms x86))
                            x86)))
                 (mv -1 x86))))))

        (mv new-offset x86)))

  (define syscall-lseek (fd offset whence x86)
    :inline nil
    :guard (and (natp fd)
                (integerp offset)
                (natp whence))
    (declare (ignorable fd offset whence x86))
    (syscall-lseek-logic fd offset whence x86)

    ///

    (local (in-theory (e/d (syscall-lseek-logic) ())))

    (defthm integerp-mv-nth-0-syscall-lseek
      (integerp (mv-nth 0 (syscall-lseek fd offset whence x86)))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-1-syscall-lseek
      (implies (and (x86p x86)
                    (natp fd))
               (x86p (mv-nth 1 (syscall-lseek fd offset whence x86))))))

  (define syscall-fadvise64-logic (fd offset len advice x86)
    (declare (ignorable fd offset len advice x86))
    (pop-x86-oracle x86))

  (define syscall-fadvise64 (fd offset len advice x86)
    :inline nil
    (declare (ignorable fd offset len advice x86))
    (syscall-fadvise64-logic fd offset len advice x86))

  (define syscall-link-logic (oldpath newpath x86)
    (declare (ignorable oldpath newpath x86))
    (pop-x86-oracle x86))

  (define syscall-link (oldpath newpath x86)
    :inline nil
    (declare (ignorable oldpath newpath x86))
    (syscall-link-logic oldpath newpath x86))

  (define syscall-unlink-logic (path x86)
    (declare (ignorable path x86))
    (pop-x86-oracle x86))

  (define syscall-unlink (path x86)
    :inline nil
    (declare (ignorable path x86))
    (syscall-unlink-logic path x86))

  (define syscall-dup-logic (oldfd x86)

    :long "<p>From the @('dup(2)') man page (Linux):</p>

    <code>int dup(int oldfd);</code>

    <p>@('dup()') uses the lowest-numbered unused descriptor for the
    new descriptor.</p>"

    :guard (integerp oldfd)
    (declare (ignorable oldfd x86))

    (b* (
         ;; Get the name and offset of the object using oldfd, the file
         ;; descriptor:
         (obj-fd-field (read-x86-file-des oldfd x86))
         ((when (not (file-descriptor-fieldp obj-fd-field)))
          (b* ((- (cw "~%Error: File Descriptor Field ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions.~%~%"))
               (x86 (!ms (list (rip x86)
                               "File Descriptor Field ill-formed. Maybe these books were ~
not built with X86ISA_EXEC set to t? See :doc x86isa-build-instructions."
                               (ms x86))
                         x86)))
              (mv -1 x86)))
         ((mv newfd x86) (pop-x86-oracle x86))
         ((when (not (integerp newfd)))
          (b* ((- (cw "~%Error: New file descriptor not an integer.~%~%"))
               (x86 (!ms (list (rip x86)
                               "New file descriptor not an integer"
                               newfd
                               (ms x86))
                         x86)))
              (mv -1 x86))))
        (mv newfd x86)))

  (define syscall-dup (oldfd x86)
    :inline nil
    :guard (integerp oldfd)
    (declare (ignorable oldfd x86))
    (syscall-dup-logic oldfd x86)
    ///

    (local (in-theory (e/d (syscall-dup-logic) ())))

    (defthm integerp-mv-nth-0-syscall-dup
      (integerp (mv-nth 0 (syscall-dup oldfd x86)))
      :rule-classes :type-prescription)

    (defthm x86p-mv-nth-1-syscall-dup
      (implies (x86p x86)
               (x86p (mv-nth 1 (syscall-dup oldfd x86))))))

  (define syscall-dup2-logic (oldfd newfd x86)
    :long "<p>From the @('dup(2)') man page (Linux):</p>

    <tt>int dup2(int oldfd, int newfd);</tt>

    <p>@('dup2()') makes newfd be the copy of <tt>oldfd</tt>, closing
    <tt>newfd</tt> first if necessary, but note the following:</p>

<ul>
    <li> If <tt>oldfd</tt> is not a valid file descriptor, then the call fails,
      and <tt>newfd</tt> is not closed.</li>

    <li> If <tt>oldfd</tt> is a valid file descriptor, and
      <tt>newfd</tt> has the same value as <tt>oldfd</tt>, then
      @('dup2()') does nothing, and returns <tt>newfd</tt>.</li>
</ul>

    <p>After a successful return from one of these system calls, the
    old and new file descriptors may be used interchangeably.  They
    refer to the same open file description (see @('open(2)')) and
    thus share file offset and file status flags; for example, if the
    file offset is modified by using @('lseek(2)') on one of the
    descriptors, the offset is also changed for the other.</p>

    <p>The two descriptors do not share file descriptor flags (the
    close-on-exec flag).  The close-on-exec flag (<tt>FD_CLOEXEC</tt>;
    see @('fcntl(2)')) for the duplicate descriptor is off.</p>"

    ;; TO-DO@Shilpi: I could make the value of the :OFFSET field a list
    ;; and the :MODE can be a corresponding list.


    :guard (and (integerp oldfd)
                (integerp newfd))
    (declare (ignorable oldfd newfd x86))
    (pop-x86-oracle x86))

  (define syscall-dup2 (oldfd newfd x86)
    :inline nil
    :guard (and (integerp oldfd)
                (integerp newfd))
    (declare (ignorable oldfd newfd x86))
    (syscall-dup2-logic oldfd newfd x86))

  (define syscall-dup3-logic (oldfd newfd flags x86)
    ;; dup3 is Linux-specific.
    (declare (ignorable oldfd newfd flags x86))
    (pop-x86-oracle x86))

  (define syscall-dup3 (oldfd newfd flags x86)
    ;; dup3 is Linux-specific.
    :inline nil
    (declare (ignorable oldfd newfd flags x86))
    (syscall-dup3-logic oldfd newfd flags x86))

  (define syscall-stat-logic (path buf x86)
    (declare (ignorable path buf x86))
    (pop-x86-oracle x86))

  (define syscall-stat (path buf x86)
    :inline nil
    (declare (ignorable path buf x86))
    (syscall-stat-logic path buf x86))

  (define syscall-lstat-logic (path buf x86)
    (declare (ignorable path buf x86))
    (pop-x86-oracle x86))

  (define syscall-lstat (path buf x86)
    :inline nil
    (declare (ignorable path buf x86))
    (syscall-lstat-logic path buf x86))

  (define syscall-fstat-logic (fd buf x86)
    (declare (ignorable fd buf x86))
    (pop-x86-oracle x86))

  (define syscall-fstat (fd buf x86)
    :inline nil
    (declare (ignorable fd buf x86))
    (syscall-fstat-logic fd buf x86))

  (define syscall-fcntl-logic (fd cmd arg x86)
    (declare (ignorable fd cmd arg x86))
    (pop-x86-oracle x86))

  (define syscall-fcntl (fd cmd arg x86)
    :inline nil
    (declare (ignorable fd cmd arg x86))
    (syscall-fcntl-logic fd cmd arg x86))

  (define syscall-truncate-logic (path length x86)
    (declare (ignorable path length x86))
    (pop-x86-oracle x86))

  (define syscall-truncate (path length x86)
    :inline nil
    (declare (ignorable path length x86))
    (syscall-truncate-logic path length x86))

  (define syscall-ftruncate-logic (fd length x86)
    (declare (ignorable fd length x86))
    (pop-x86-oracle x86))

  (define syscall-ftruncate (fd length x86)
    :inline nil
    (declare (ignorable fd length x86))
    (syscall-ftruncate-logic fd length x86))

  (push-untouchable (
                     syscall-read-logic
                     syscall-write-logic
                     syscall-open-logic
                     syscall-close-logic
                     syscall-stat-logic
                     syscall-lstat-logic
                     syscall-fstat-logic
                     syscall-lseek-logic
                     syscall-fadvise64-logic
                     syscall-link-logic
                     syscall-unlink-logic
                     syscall-dup-logic
                     syscall-dup2-logic
                     syscall-fcntl-logic
                     syscall-truncate-logic
                     syscall-ftruncate-logic
                     syscall-dup3-logic
                     )
                    t)

  )

;; ======================================================================

;; Exec definitions:

(defmacro build-with-full-exec-support (no-skip? exec-type event alt-event)
  ;; A macro that is replaced by "event" if both of these are true:
  ;; "no-skip?" is non-nil and function "exec-type" is defined;
  ;; otherwise, "alt-event" is the result.
  `(make-event (if (and ,no-skip? (function-symbolp ',exec-type (w state)))
                   (value ',event)
                 (value ',alt-event))))

(defmacro supported-platform? ()
  ;; Linux system:
  #+(and linux (not darwin) (not freebsd))
  t
  ;; Darwin system:
  #+(and darwin (not linux) (not freebsd))
  t
  ;; FreeBSD system:
  #+(and freebsd (not darwin) (not linux))
  t
  ;; Other (e.g., Windows):
  #+(and (not linux) (not darwin) (not freebsd))
  nil)

(defmacro OS (l d f)
  ;; Linux system:
  #+(and linux (not darwin) (not freebsd))
  (declare (ignore d) (ignore f))
  #+(and linux (not darwin) (not freebsd))
  l

  ;; Darwin system:
  #+(and darwin (not linux) (not freebsd))
  (declare (ignore l) (ignore f))
  #+(and darwin (not linux) (not freebsd))
  d

  ;; FreeBSD system, for which we do what's done on a Darwin system
  ;; for now:
  #+(and freebsd (not darwin) (not linux))
  (declare (ignore l) (ignore f))
  #+(and freebsd (not darwin) (not linux))
  d ;; TODO: f, one day.

  ;; Other (e.g., Windows):
  #+(and (not linux) (not darwin) (not freebsd))
  (declare (ignore l) (ignore d) (ignore f))
  #+(and (not linux) (not darwin) (not freebsd))
  ;; Unsupported platform: syscall simulation in application-level view
  ;; unavailable!
  nil)

(defsection syscalls-exec
  :parents (syscalls)
  :short "Syscall definitions to be used in the application-level view
  for execution"

  :long "<p>The definitions of the following <em>(not inlined)</em>
  functions in ACL2 have been smashed in raw Lisp; see the book
  @('environment-and-syscalls-raw.lsp') for the raw Lisp
  definitions.  These raw Lisp definitions are used when doing
  execution, and the ACL2 definitions are used when reasoning.</p>

<p><b>IMPORTANT:</b> The following raw Lisp definitions will not be
available unless the x86 books have been build with the environment
variable @('X86ISA_EXEC') set to @('t'). See @(see
x86isa-build-instructions) for details.</p>

<ul>
<li>@(see env-read)</li>
<li>@(see env-write)</li>
<li>@(see read-x86-file-des)</li>
<li>@(see read-x86-file-contents)</li>
<li>@(see write-x86-file-des)</li>
<li>@(see delete-x86-file-des)</li>
<li>@(see write-x86-file-contents)</li>
<li>@(see delete-x86-file-contents)</li>
<li>@(see pop-x86-oracle)</li>
<li>@(see syscall-read)</li>
<li>@(see syscall-write)</li>
<li>@(see syscall-open)</li>
<li>@(see syscall-close)</li>
<li>@(see syscall-lseek)</li>
<li>@(see syscall-fadvise64)</li>
<li>@(see syscall-link)</li>
<li>@(see syscall-unlink)</li>
<li>@(see syscall-dup)</li>
<li>@(see syscall-dup2)</li>
<li>@(see syscall-fcntl)</li>
<li>@(see syscall-truncate)</li>
<li>@(see syscall-ftruncate)</li>
<li>@(see syscall-stat)</li>
<li>@(see syscall-fstat)</li>
<li>@(see syscall-lstat)</li>
</ul> "

  (build-with-full-exec-support

   ;; The top-level Makefile for these x86isa books (../Makefile)
   ;; write out syscalls.acl2 when X86ISA_EXEC=t.  This file contains
   ;; the definition of the function x86isa_syscall_exec_support,
   ;; which we provide as the first argument of the macro
   ;; build-with-full-exec-support.  If this function is undefined
   ;; (i.e., if the x86 books are not certified using the accompanying
   ;; Makefile or if X86ISA_EXEC=nil), then
   ;; build-with-full-exec-support will return its third argument.
   ;; Otherwise, it will return its first argument.

   (supported-platform?)

   x86isa_syscall_exec_support

   (progn

     (defttag :syscall-exec)

     (make-event
      ;; Record the current working directory.
      `(defconst *current-dir* ',(cbd)))

     (defconst *os-specific-dynamic-lib*
       (os
        "shared/libsyscallutils.so"    ;; Linux
        "shared/libsyscallutils.dylib" ;; Darwin
        ;; Hopefully, one day I'll have FreeBSD listed here as well.
        ""))

     (defconst *shared-syscall-dir-path*
       (string-append *current-dir* *os-specific-dynamic-lib*))

; Instruction to cert.pl for dependency tracking.
; (depends-on "environment-and-syscalls-raw.lsp")

     (include-raw "environment-and-syscalls-raw.lsp"))

   (value-triple
    (cw "~%~%X86ISA_EXEC Warning: environment-and-syscalls-raw.lsp is not included.~%~%~%"))))

;; ======================================================================

(defsection x86-syscall-args-and-return-value-marshalling
  :parents (syscalls)
  :short "Collecting arguments to system calls from the x86 state and
  retrieving the return value"

  :long "<p>Source: System V Application Binary Interface AMD64 Architecture
Processor Supplement (Draft Version 0.99.6, July 2, 2012) --- also
called x64 ABI informally. Edited by Michael Matz, Jan Hubic ka,
Andreas Jaeger, Mark Mitchell</p>

<p>The Linux AMD64 kernel uses internally the same calling conventions
as user-level applications... User-level applications that like to
call system calls should use the functions from the C library. The
interface between the C library and the Linux kernel is the same as
for the user-level applications with the following differences:</p>

<ol>
<li> User-level applications use as integer registers for passing the
sequence @('%rdi'), @('%rsi'), @('%rdx'), @('%rcx'), @('%r8') and
@('%r9'). The kernel interface uses @('%rdi'), @('%rsi'), @('%rdx'),
@('%r10'), @('%r8') and @('%r9'). </li>

<li> A system-call is done via the syscall instruction. The kernel
destroys registers @('%rcx') and @('%r11').</li>

<li> The number of the syscall has to be passed in register
@('%rax').</li>

<li> System-calls are limited to six arguments, no argument is passed
directly on the stack. </li>

<li> Returning from the syscall, register @('%rax') contains the
result of the system-call. A value in the range between -4095 and -1
indicates an error, it is @('-errno'). </li>

<li> Only values of class @('INTEGER') or class @('MEMORY') are passed
to the kernel.</li>
</ol>
"

  (define x86-syscall-read (x86)
    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard)

    ;; ssize_t read(int fd, void *buf, size_t count);

    ;; RAX: 0
    ;; RDI: file descriptor
    ;; RSI: address of buffer where the read contents will be stored
    ;; RDX: number of bytes to be read

    ;; On return:
    ;; RAX: Error, if any

    (b* ((ctx 'x86-syscall-read)
         (fd (rr64 *rdi* x86))
         ;; Address ought to be read using rgfi instead of rr64.
         (*buf (rgfi *rsi* x86))
         (count (rr64 *rdx* x86))

         ((mv ret x86)
          (syscall-read fd *buf count x86))
         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-write (x86)

    ;; ssize_t write(int fd, void *buf, size_t count);

    ;; RAX: 1
    ;; RDI: file descriptor where data will be written
    ;; RSI: address of buffer from where data will be read
    ;; RDX: number of bytes to be written

    ;; On return:
    ;; RAX: Error, if any

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard)


    (b* ((ctx 'x86-syscall-write)
         (fd (rr64 *rdi* x86))
         ;; Address ought to be read using rgfi instead of rr64.
         (*buf (rgfi *rsi* x86))
         (count (rr64 *rdx* x86))

         ((mv ret x86)
          (syscall-write fd *buf count x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         (x86 (!rgfi *rax* ret x86)))

      x86))

  (define x86-syscall-open (x86)

    ;; int open (const char* path-ptr, int flags, mode_t mode);

    ;; RAX: 2
    ;; RDI: address of 0-terminated pathname
    ;; RSI: flags
    ;; RDX: mode

    ;; On return:
    ;; RAX: File descriptor or error

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard)

    (b* ((ctx 'x86-syscall-open)
         ;; Address ought to be read using rgfi instead of rr64.
         (path-ptr (rgfi *rdi* x86))
         (flags   (rr64 *rsi* x86))
         (mode     (rr64 *rdx* x86))

         ;; path-ptr sanity check
         ((when (not (canonical-address-p path-ptr)))
          (!ms :syscall-open-path-ptr-not-canonical x86))

         ((mv flg path x86)
          (read-string-zero-terminated path-ptr x86))
         ((when flg)
          (!ms (list ctx :path flg) x86))

         ((mv ret x86)
          (syscall-open path flags mode x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))

      x86))

  (define x86-syscall-close (x86)

    ;; int close (int fd);

    ;; RAX: 3
    ;; RDI: File descriptor

    ;; On return:
    ;; RAX: Error, if any

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard)

    (b* ((ctx 'x86-syscall-close)
         (fd (rr64 *rdi* x86))

         ((mv ret x86)
          (syscall-close fd x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))

      x86))

  (define x86-syscall-lseek (x86)

    ;; off_t lseek(int fd, off_t offset, int whence);

    ;; RAX: 7
    ;; RDI: File descriptor
    ;; RSI: Offset to seek to
    ;; RDX: The way seek the seek is done

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard)

    (b* ((ctx 'x86-syscall-lseek)
         (fd (rr64 *rdi* x86))

         (offset (rgfi *rsi* x86))
         (whence (rr64 *rdx* x86))

         ((mv ret x86)
          (syscall-lseek fd offset whence x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))

      x86))

  (define x86-syscall-fadvise64 (x86)

    ;; int fadvise64(int fd, off_t offset, off_t len, int advice);

    ;; RAX: 221
    ;; RDI: File descriptor
    ;; RSI: Offset to seek to
    ;; RDX: len
    ;; R10: advice

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-fadvise64
                                                   syscall-fadvise64-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-fadvise64)
         (fd (rr64 *rdi* x86))

         (offset (rgfi *rsi* x86))
         (len (rgfi *rdx* x86))
         (advice (rgfi *r10* x86))

         ((mv ret x86)
          (syscall-fadvise64 fd offset len advice x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))

      x86))


  (define x86-syscall-link (x86)

    ;; int link(const char* oldpath, const char* newpath);
    ;; RAX: 86
    ;; RDI: Path to existing file
    ;; RSI: Path to newly created hard link

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-link
                                                   syscall-link-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-link)
         (old-path-ptr (rgfi *rdi* x86))
         (new-path-ptr (rgfi *rsi* x86))

         ;; old-path-ptr sanity check
         ((when (not (canonical-address-p old-path-ptr)))
          (!ms (list ctx :syscall-link-oldpath-ptr-overflow) x86))

         ((mv flg old-path x86)
          (read-string-zero-terminated old-path-ptr x86))
         ((when flg)
          (!ms (list ctx :old-path flg) x86))

         ;; new-path-ptr sanity check
         ((when (not (canonical-address-p new-path-ptr)))
          (!ms (list ctx :syscall-link-newpath-ptr-overflow) x86))

         ((mv flg new-path x86)
          (read-string-zero-terminated new-path-ptr x86))
         ((when flg)
          (!ms (list ctx :new-path flg) x86))

         ((mv ret x86)
          (syscall-link old-path new-path x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))

      x86))

  (define x86-syscall-unlink (x86)

    ;; int unlink(const char* path);
    ;; RAX: 87
    ;; RDI: Path to existing hard link

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-unlink
                                                   syscall-unlink-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-unlink)
         (path-ptr (rgfi *rdi* x86))

         ;; path-ptr sanity check
         ((when (not (canonical-address-p path-ptr)))
          (!ms (list ctx :syscall-link-path-ptr-overflow) x86))

         ((mv flg path x86)
          (read-string-zero-terminated path-ptr x86))
         ((when flg)
          (!ms (list ctx :path flg) x86))

         ((mv ret x86)
          (syscall-unlink path x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx :oracle-val-for-syscall-unlink ret) x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))

      x86))


  (define x86-syscall-dup (x86)

    ;; int dup(int oldfd)
    ;; RAX: 32
    ;; RDI: Old file descriptor

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-dup
                                                   syscall-dup-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-dup)
         (oldfd (rgfi *rdi* x86))

         ((mv ret x86)
          (syscall-dup oldfd x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx :oracle-val-for-syscall-dup ret) x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-dup2 (x86)

    ;; int dup2(int oldfd, int newfd);
    ;; RAX: 33
    ;; RDI: Old file descriptor
    ;; RSI: New file descriptor

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-dup2
                                                   syscall-dup2-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-dup2)
         (oldfd (rgfi *rdi* x86))
         (newfd (rgfi *rsi* x86))

         ((mv ret x86)
          (syscall-dup2 oldfd newfd x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-dup3 (x86)

    ;; int dup3(int oldfd, int newfd, int flags);
    ;; RAX: 292
    ;; RDI: Old file descriptor
    ;; RSI: New file descriptor
    ;; RDX: Flags

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-dup3
                                                   syscall-dup3-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-dup3)
         (oldfd (rgfi *rdi* x86))
         (newfd (rgfi *rsi* x86))
         (flags (rgfi *rdx* x86))

         ((mv ret x86)
          (syscall-dup3 oldfd newfd flags x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-stat (x86)

    ;; int stat(const char* path, struct stat* statbuf);
    ;; RAX: 4
    ;; RDI: Address of the path
    ;; RSI: Address to a pre allocated structure

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-stat
                                                   syscall-stat-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-stat)
         (path (rgfi *rdi* x86))
         (statBuf (rgfi *rsi* x86))

         ;; path sanity check
         ((when (not (canonical-address-p path)))
          (!ms (list ctx :syscall-stat-path-ptr-not-canonical) x86))

         ((mv flg pathname x86)
          (read-string-zero-terminated path x86))
         ((when flg)
          (!ms (list ctx :path flg) x86))

         ((mv ret x86)
          (syscall-stat pathname statBuf x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx :oracle-val-for-syscall-stat ret) x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-lstat (x86)

    ;; int lstat(const char* path, struct stat* statbuf);
    ;; RAX: 6
    ;; RDI: Address of the path of a link
    ;; RSI: Address to a pre allocated structure

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-lstat
                                                   syscall-lstat-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-lstat)
         (path (rgfi *rdi* x86))
         (statBuf (rgfi *rsi* x86))

         ;; path sanity check
         ((when (not (canonical-address-p path)))
          (!ms (list ctx :syscall-lstat-path-ptr-not-canonical) x86))

         ((mv flg pathname x86)
          (read-string-zero-terminated path x86))
         ((when flg)
          (!ms (list ctx :path flg) x86))

         ((mv ret x86)
          (syscall-lstat pathname statBuf x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx :oracle-val-for-syscall-lstat ret) x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-fstat (x86)

    ;; int fstat(int fd, struct stat* statbuf);
    ;; RAX: 5
    ;; RDI: Descriptor of the file to stat
    ;; RSI: Address to a pre allocated structure

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-fstat
                                                   syscall-fstat-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-fstat)
         (fd (rgfi *rdi* x86))
         (statBuf (rgfi *rsi* x86))

         ((mv ret x86)
          (syscall-fstat fd statBuf x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-fcntl (x86)

    ;; int fcntl(unsigned int fd, unsigned int cmd, unsigned long arg);
    ;; RAX: 72
    ;; RDI: The file descriptor
    ;; RSI: The operation
    ;; RDX: The argument

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-fcntl
                                                   syscall-fcntl-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-fcntl)
         (fd (rgfi *rdi* x86))
         (cmd (rgfi *rsi* x86))
         (arg (rgfi *rdx* x86))

         ((mv ret x86)
          (syscall-fcntl fd cmd arg x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-truncate (x86)

    ;; int truncate(const char* path, long length);
    ;; RAX: 76
    ;; RDI: The address of the path
    ;; RSI: The length to truncate to

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-truncate
                                                   syscall-truncate-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-truncate)
         (path (rgfi *rdi* x86))
         (length (rgfi *rsi* x86))

         ;; path sanity check
         ((when (not (canonical-address-p path)))
          (!ms (list ctx :syscall-truncate-path-ptr-not-canonical) x86))

         ((mv flg pathname x86)
          (read-string-zero-terminated path x86))
         ((when flg)
          (!ms (list ctx :path flg) x86))

         ((mv ret x86)
          (syscall-truncate pathname length x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx :oracle-val-for-syscall-truncate ret) x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86))

  (define x86-syscall-ftruncate (x86)

    ;; int ftruncate(unsigned int fd, unsigned long length);
    ;; RAX: 77
    ;; RDI: The file descriptor
    ;; RSI: The length to truncate to

    :parents (x86-syscall-args-and-return-value-marshalling)
    :returns (x86 x86p :hyp :guard
                  :hints (("Goal" :in-theory (e/d (syscall-ftruncate
                                                   syscall-ftruncate-logic)
                                                  (force (force))))))

    (b* ((ctx 'x86-syscall-ftruncate)
         (fd (rgfi *rdi* x86))
         (length (rgfi *rsi* x86))

         ((mv ret x86)
          (syscall-ftruncate fd length x86))

         ((when (or (ms x86)
                    (not (i64p ret))))
          (!ms (list ctx
                     :ret-val-or-ms-for-syscall-write
                     ret)
               x86))

         ;; Save return code to rax
         (x86 (!rgfi *rax* ret x86)))
      x86)))

;; ======================================================================
