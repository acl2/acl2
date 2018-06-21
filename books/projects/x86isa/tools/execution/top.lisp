;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "init-page-tables" :ttags :all)
(include-book "../../proofs/utilities/row-wow-thms" :ttags :all)
(include-book "exec-loaders/elf/elf-reader" :ttags :all)
(include-book "exec-loaders/mach-o/mach-o-reader" :ttags :all)
(include-book "instrument/top" :ttags :all)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defxdoc program-execution
  :parents (X86ISA)

  :short "Setting up the x86 ISA model for a program run"

  :long "<p>IMPORTANT: Note that if these books were built using any
  other value of @('X86ISA_EXEC') except @('t'), then instructions
  like @('SYSCALL') and @('RDRAND') will not be available for
  execution, though reasoning about them will still be possible. See
  @(see x86isa-build-instructions) for details.</p>

<p>First, obtain the x86 machine-code version of the program
you want to execute on the model. Note that we support only <a
href=\"http://en.wikipedia.org/wiki/Executable_and_Linkable_Format\">ELF</a>
\(created on Linux machines\) and <a
href=\"http://en.wikipedia.org/wiki/Mach-O\">Mach-O</a> binaries
\(created on Darwin/Apple machines\).</p>

<p>Here is a sample popcount program in C that will be used for
illustration throughout this section.</p>

<code>
// FILENAME: popcount.c
// From Sean Anderson's Bit Twiddling Hacks
// See https://graphics.stanford.edu/~seander/bithacks.html

#include @('<stdio.h>')
#include @('<stdlib.h>')

int popcount_32 (unsigned int v) \{
  v = v - ((v @('>>') 1) @('&') 0x55555555);
  v = (v @('&') 0x33333333) + ((v @('>>') 2) @('&') 0x33333333);
  v = ((v + (v @('>>') 4) @('&') 0xF0F0F0F) * 0x1010101) @('>>') 24;
  return(v);
\}

int main (int argc, char *argv[], char *env[]) \{
  int v;
  printf (\"\\nEnter a 32-bit number: \");
  scanf  (\"%d\", @('&')v);
  v = v @('&') 0xffffffff;
  printf (\"\\nPopcount of %d is: %d\\n\", v, popcount_32(v));
  return 0;
\}
</code>

<p>We can use the following command to obtain the x86 binary
corresponding to this program; we will call this binary
@('popcount.o').</p>

<code>
gcc popcount.c -o popcount.o
</code>

<p>You can see the assembly and machine code corresponding to this
program using utilities like @('objdump') on Linux machines and
@('otool') on Mac machines.  Example invocations are as follows:</p>

<p>On Linux machines:</p>
<code>
objdump -d popcount.o
</code>
<p>On Mac machines:</p>
<code>
otool -tvj popcount.o
</code>

<p><b>Note that the assembly and machine code can differ from machine
to machine, program run to program run.  All the concrete values of
addresses, etc. used in this example can be different for you.</b></p>

<p>The following events describe the process of setting up the x86 ISA
  model for the execution of @('popcount.o').</p>

<ol>

<li><p>Include the top-level book \(i.e., X86ISA/top.lisp\) in a fresh
ACL2 session.</p>

<code>(include-book \"top\" :ttags :all)</code>

<p>Alternatively, it can be faster to just include
tools/execution/top.lisp.</p>

<code>(include-book \"tools/execution/top\" :ttags :all)</code>

<p>You should always be in the @('X86ISA') package when working with
the x86 books.  If you start an ACL2 session when standing under any
of the x86 directories, your ACL2 session will start in the
@('X86ISA') package.  Otherwise, you also need the following form
after the above @('include-book').</p>

<code>
(in-package \"X86ISA\")
</code>

</li>

<li> If you desire to run the model in the @(see
app-view), skip this step.  Use the function @(see
init-sys-view) to switch the model to the system-level view
and load our default configuration of 1G page tables \(set up to
provide an identity mapping from linear to physical addresses\) into
the model's memory at the provided address, i.e., @('0x0') in our
example.  Of course, this is a contrived example.  For more
flexibility in constructing and loading page tables, see @(csee
Setting-up-Page-Tables).

<code>
(init-sys-view 0 x86)
</code>
</li>

<li><p>Read and load @('popcount.o') into the x86 model's memory using the
macro @('binary-file-load').</p>

<code> (binary-file-load \"popcount.o\") </code>

<p>@('binary-file-load') will fail if @('popcount.o') is not a supported
ELF or Mach-O file.</p>
</li>

<li><p>Use @(see init-x86-state) to modify other components of the x86
state, like the instruction pointer, registers, arguments in memory,
if necessary.  Note that @('init-x86-state') only writes the specified
values into the x86 state while preserving any values previously
written to the x86 state.  For example, the following form will
<i>not</i> make changes to any general-purpose registers except
@('rdi') and @('rsp').</p>

<code>
(init-x86-state
 ;; Status (MS and fault field)
 nil
 ;; Start Address --- set the RIP to this address
 #x100000f12
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 #x100000f17
 ;; Initial values of General-Purpose Registers
 '((#.*rdi* . #xff00ff00)
   (#.*rsp* . #.*2^45*))
 ;; Control Registers: a value of nil will not nullify existing
 ;; values.
 nil
 ;; Model-Specific Registers: a value of nil will not nullify existing
 ;; values.
 nil
 ;; Segment Registers: a value of nil will not nullify existing values.
 nil ; visible portion
 nil ; hidden portion
 ;; Rflags Register
 2
 ;; Memory image: a value of nil will not nullify existing values.
 nil
 ;; x86 state
 x86)
</code>

<p><b>Aside</b>: Some other ways to initialize the x86 state are
listed below.  The list is not exhaustive.</p>

<ul>

<li><p>The memory image argument of @(see init-x86-state) accepts
alists satisfying @(see n64p-byte-alistp).  This can be used to
provide a program binary in the form of a list of address-byte pairs
rather using @('binary-file-load') to parse and load the binary
automatically.</p></li>

<li><p>The function @(see load-program-into-memory) also accepts
programs that satisfy @('n64p-byte-alistp').</p></li>

<li><p>Of course, @(see wml08) \(and its friends like @(see
write-bytes-to-memory)\) can also be used to write a program to the
memory.  Initialization of other components of the x86 state can be
done by using the appropriate updater functions directly.  For
example, @('!stri') can be used to update system registers like
@('GDTR') and @('IDTR') when operating in the system-level
view.</p></li>

</ul>

<p>All the mechanisms to initialize the x86 state aside, how do we
know what values to put in the x86 state?  This is an important and
interesting question.  Its answer depends on the program \(or snippet
of a program\) we intend to execute and requires the user to be
familiar with x86 assembly and calling conventions. For this popcount
example, suppose all we wanted to execute was the @('popcount_32')
routine with an actual concrete argument, say @('0xff00ff00'). One way
to figure out what the start and halt addresses should be in this case
is to look at the output from @('objdump') or @('otool') for
instructions in the @('main') routine that look like the
following:</p>

<code>
...
100000f10: 89 c7                mov    %eax,%edi
100000f12: e8 49 ff ff ff       callq  100000e60 @('<_popcount_32>')
100000f17: 48 8d 3d 66 00 00 00 lea    0x66(%rip),%rdi
...
</code>

<p>We set the start address to be the address of the instruction that
calls the @('popcount_32') function \(i.e., @('0x100000f12') here\)
and halt address to be the address of the instruction following it
\(i.e., @('0x100000f17') here\).</p>

<p>Before entering @('popcount_32'), the component of the x86 state
that contains the concrete argument \(i.e., @('0xff00ff00') in our
example\) should be initialized appropriately too. How do we know
which component is used for this purpose?  Knowledge of calling
conventions can help here --- for example, on 64-bit Linux, if the
argument is of the integer type, then the next available register of
the following sequence is used for argument passing: @('rdi'),
@('rsi'), @('rdx'), @('rcx'), @('r8'), and @('r9').  For more details,
see <a href=\"http://www.x86-64.org/documentation/abi.pdf\">this</a>
and <a
href=\"http://www.agner.org/optimize/calling_conventions.pdf\">this</a>.
For our example program, the register @('rdi') \(more accurately,
register @('edi') --- the lower 32 bits of the register @('rdi')\) is
used to pass the concrete argument to @('popcount_32').  We can
confirm this by inspecting the assembly.  For example, in the
@('main') routine, before the call to @('popcount_32'), we might
observe an instruction that moves the argument to @('edi') --- see the
instruction at address @('100000f10') in the assembly snippet above.
Another clue can be the assembly corresponding to the @('popcount_32')
routine, where we might see an instruction moving the value in
@('edi') to the stack --- see the instruction at address
@('100000e64') below.</p>

<code>
...
0000000100000e60 @('<_popcount_32>'):
   100000e60:	55                     push   %rbp
   100000e61:	48 89 e5               mov    %rsp,%rbp
   100000e64:	89 7d fc               mov    %edi,-0x4(%rbp)
...
</code>

<p>It should be emphasized is that it is the user's responsibility to
ensure that the state is initialized \"correctly\", i.e., the program
does not overlap with the page tables, the stack pointer is
initialized so that the stack does not run out of memory nor does it
overwrite the program during execution \(in our example, @('2^45') is
the initial value of the stack pointer for this very reason\), etc.
Essentially, the user takes on the job of the operating system plus
the compiler/linker, etc.  Unless the program of choice is being
executed \"on top of\" these system programs which are also being
executed on the model, there is probably no way to remove this burden
from the user.</p>

</li>

<li>

<p>Run the program using @(see x86-run) or @(see x86-run-steps);
@('x86-run') returns only the modified x86 state and @('x86-run-step')
returns the number of instructions actually executed as well as the
modified x86 state. To run one instruction only, use @(see
x86-fetch-decode-execute).  You can also see @(see
Dynamic-instrumentation) for details about dynamically debugging the
program by inserting breakpoints and logging the x86 state into a
file, etc.</p>

<code>
(x86-run-steps 10000 x86) ;; or (x86-run 10000 x86)
</code>

<p>How do know that the program ran to completion?  After executing
the above form, we can inspect the contents of the @('ms') field:</p>

<code>
(ms x86)
</code>

<p>If the @('ms') field contains a legal halt message, we know that
the program was run successfully.  If it contains an error message, we
need to figure out what went wrong during the program execution ---
the @(see Dynamic-instrumentation) utilities can help in debugging.
If @('ms') contains @('nil'), the program did not run to completion
and the x86 state is poised to continue execution.</p>

<p>Where did the number @('10000') in the argument to @('x86-run') or
@('x86-run-steps') come from?  This number is the clock, i.e., the
upper limit on the number of instructions the x86 interpreter will
execute.  Fewer instructions that this number can be executed if the
program reached the halt address sooner or if an error is encountered
\(in which case the @('ms') field will contain the error message).  It
might also be the case that this argument to @('x86-run') or
@('x86-run-steps') is less than the number of instructions required to
run the program to completion.  So, how do we pick the value of the
clock?</p>

<p>This, again, is up to the user.  Guessing the clock value is an
answer.  In our example, @('10000') is large enough --- this example
program is small enough that it takes only around a couple dozen
instructions to run to completion.  You need not worry about the
interpreter stepping uselessly after the program halts \(or encounters
an error\) because then, the @('ms') field will contain a message and
@('x86-run') and @('x86-run-steps') will stop executing as soon as the
@('ms') field is non-nil.  On the other hand, if the clock you
provided is not sufficient \(@('ms') is nil\), then you can always
execute @('x86-run') or @('x86-run-steps') again and the program
execution will continue.</p>

</li>

<li>

<p>Inspect the output of the program.  For this program, register
@('eax') contains the return value --- x86-64 Linux calling
conventions dictate that @('rax') be the first return register.  Of
course, as before, we can inspect the assembly to confirm if this is
the case.</p>

<code>
(rgfi *rax* x86) ;; Note that eax is the low 32 bits of rax.
</code>

<p>For the value @('0xff00ff00'), the register @('rax') should contain
16.</p>

<p>If you wish to run this program again in the same ACL2 session,
remember to initialize the x86 state appropriately.</p>

</li>

</ol>"

  )

(local (xdoc::set-default-parents program-execution))

;; ======================================================================

(define binary-file-load-fn (filename elf mach-o x86 state)
  :parents (program-execution)
  :short "Function to read in an ELF or Mach-O binary and load it into
  the x86 ISA model's memory"
  :long "<p>The following macro makes it convenient to call this
  function to load a program:</p>
<code> (binary-file-load \"fib.o\") </code>"

  :guard (stringp filename)
  :verify-guards nil

  (b* (((mv file-byte-list state)
        (ACL2::read-file-bytes filename state))

       ((when (or (not (byte-listp file-byte-list))
                  (equal file-byte-list nil)))
        (mv nil (cw "Error in reading file ~p0.~%" filename)
            elf mach-o x86 state))

       (file-header (take 64 file-byte-list))
       ((when (not (byte-listp file-header)))
        (mv
         nil
         (cw "File ~p0: Header could not be read.~%" filename)
         elf mach-o x86 state))

       (- (cw "~%Reading the header of the file to determine its type...~%"))
       ((mv flg type)
        (b* ((elf-header (read-elf-header file-header))
             (magic (combine-bytes (cdr (assoc 'magic elf-header))))
             (class (cdr (assoc 'class elf-header)))
             ((when (and (equal magic #.*ELFMAG*)
                         (equal class 2)))
              (mv nil 'ELF))
             (mach-o-header (read-mach_header (take 32 file-header)))
             (magic (nfix (cdr (assoc 'MAGIC mach-o-header))))
             ((when (or (equal magic #.*MH_MAGIC*)
                        (equal magic #.*MH_CIGAM*)
                        (equal magic #.*MH_MAGIC_64*)
                        (equal magic #.*MH_CIGAM_64*)))
              (mv nil 'MACH-O)))
            (mv t nil)))
       ((when flg)
        (mv nil
            (cw "Error: Not an ELF or Mach-O object file (as suggested by the magic number).~%")
            elf mach-o x86 state))
       (- (cw "~%File type is detected to be: ~p0.~%" type))

       (- (cw "~%Reading and parsing ~p0...~%" filename))
       ((mv alst elf mach-o state)
        (if (equal type 'ELF)
            (b* (((mv alst elf state)
                  (elf-file-read file-byte-list elf state)))
                (mv alst elf mach-o state))
          (b* (((mv alst mach-o state)
                (mach-o-file-read file-byte-list mach-o state)))
              (mv alst elf mach-o state))))
       (- (cw "~%File ~p0 read complete.~%" filename))

       (- (cw "~%Loading sections of ~p0 in the memory of the x86 model...~%" filename))
       ((mv flg x86)
        (if (equal type 'ELF)
            (b* (((mv flg0 x86)
                  (elf-load-text-section elf x86))
                 ((mv flg1 x86)
                  (elf-load-data-section elf x86)))
                (mv (and flg0 flg1) x86))
          (b* (((mv flg0 x86)
                (mach-o-load-text-section mach-o x86))
               ((mv flg1 x86)
                (mach-o-load-data-section mach-o x86)))
              (mv (and flg0 flg1) x86))))

       ((when flg)
        (mv nil
            (cw "Error encountered while loading sections in the memory of the x86 model...~%")
            elf mach-o x86 state))
       (- (cw "~%x86 model's memory initialized appropriately.~%"))
       (- (cw "~%Now printing the headers of the binary file...~%~%")))

      (mv type alst elf mach-o x86 state)))

(defmacro binary-file-load (filename)
  `(binary-file-load-fn ,filename elf mach-o x86 state))

(define init-sys-view
  ((paging-base-addr :type (unsigned-byte 52))
   x86)
  ;; TO-DO: I should have the 40-bit wide PDB as the input, instead of
  ;; the 52-bit wide physical address of the PML4 Table.

  :parents (program-execution)
  :short "Switches the model to the system-level view and load our
default configuration of 1G page tables"

  :guard (equal (loghead 12 paging-base-addr) 0)
  :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))

  :returns (x86 x86p :hyp (and (x86p x86) (unsigned-byte-p 52 paging-base-addr)))
  :prepwork
  ((local (include-book "centaur/gl/gl" :dir :system))

   (local
    (def-gl-thm init-sys-view-helper-1
      :hyp (unsigned-byte-p 64 x)
      :concl (equal (logior 32 (logand 4294967263 (loghead 21 x)))
                    (logior 32 (logand 2097119 (loghead 21 x))))
      :g-bindings (gl::auto-bindings (:nat x 64))))

   (local
    (def-gl-thm init-sys-view-helper-2
      :hyp (unsigned-byte-p 64 x)
      :concl (equal (logior 256 (logand 65279 (loghead 12 x)))
                    (logior 256 (logand 3839 (loghead 12 x))))
      :g-bindings (gl::auto-bindings (:nat x 64))))

   (local
    (def-gl-thm init-sys-view-helper-3
      :hyp (unsigned-byte-p 64 x)
      :concl (equal (logior 2147483648
                            (logand 18446744071562067967
                                    (loghead 32 x)))
                    (logior 2147483648 (loghead 31 x)))
      :g-bindings (gl::auto-bindings (:nat x 64)))))

  (b* ((ctx 'init-sys-view)
       ((when (not (equal (loghead 12 paging-base-addr) 0)))
        (!!ms-fresh :misaligned-paging-base-address paging-base-addr))
       (paging-base-addr40 (logtail 12 paging-base-addr))

       (x86
        ;; The default value of app-view is t; nil switches the model
        ;; to the system-level view.
        (!app-view nil x86))

       (cr0 (n32 (ctri #.*cr0* x86)))
       (cr4 (n21 (ctri #.*cr4* x86)))
       ;; Control registers:
       (x86 (!ctri #.*cr0* (!cr0-slice :cr0-pg 1 cr0) x86))
       (x86 (!ctri #.*cr4* (!cr4-slice :cr4-pae 1 cr4) x86))
       (x86 (!ctri #.*cr3* (!cr3-slice :cr3-pdb paging-base-addr40 (ctri #.*cr3* x86)) x86))

       ;; Model-specific registers:
       (efer (n12 (msri #.*ia32_efer-idx* x86)))
       (x86 (!msri #.*ia32_efer-idx* (!ia32_efer-slice :ia32_efer-lme 1 efer) x86))

       ;; Initializing the page tables.
       (x86
        (load-qwords-into-physical-memory-list
         (construct-page-tables paging-base-addr) x86)))
      x86))

;; ======================================================================
