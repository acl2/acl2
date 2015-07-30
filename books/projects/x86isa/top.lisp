;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; x86 ISA model specification
(include-book "machine/x86" :ttags :all)

;; Misc. tools
(include-book "tools/execution/top" :ttags :all)

;; Proof books
(include-book "proofs/top" :ttags :all)

;; For printing strings, etc.
(include-book "std/strings/top" :dir :system)

;; Files will be copied from X86ISA/x86-images to res/x86-images of
;; the x86 manual.
(xdoc::add-resource-directory "x86-images" "x86-images")

(defxdoc X86ISA
  :parents (acl2::software-verification acl2::projects)
  :short "x86 ISA model and machine-code analysis framework developed
  at UT Austin"
  )

(xdoc::order-subtopics
 X86ISA
 (Build-Instructions
  Introduction
  utils
  machine
  program-execution
  model-validation
  proof-utilities
  code-proofs
  Contributors
  Publications
  TO-DO))

(defsection Introduction
  :parents (x86isa)

  :short "High-level information about these books"

  :long "<p>These books contain the specification of x86 instruction
set architecture \(ISA\); we characterize x86 machine instructions and
model the instruction fetch, decode, and execute process using the
ACL2 theorem-proving system.  We use our x86 ISA specification to
formally verify x86 machine-code programs.</p>

<p>These books include:</p>

<ul>
<li>A formal, executable x86 ISA model \(see machine directory\)</li>
<li>General theorems to aid in machine-code verification \(see
proofs/utilities directory\)</li>
<li>Proofs of properties of various programs \(see proofs directory\)</li>
</ul>

<p>Here are some important factors that influenced almost every choice
  we made while developing these books.</p>

<ul>

<li>

<b>Completeness of the x86 Model:</b> <p>The utility of a formal ISA
model for performing machine-code verification depends directly on the
model's completeness \(with respect to the ISA features specified\),
accuracy, and reasoning and execution efficiency.  <a
href='http://www.intel.com/content/www/us/en/processors/architectures-software-developer-manuals.html'>Intel
software developer's manuals</a> were used as specification documents,
and ambiguities were resolved by cross-referencing <a
href='http://developer.amd.com/resources/documentation-articles/developer-guides-manuals/'>AMD
manuals</a> and running tests on real machines to understand processor
behavior.  There are a multitude of features in the x86 ISA that
include those left over from its early days to ensure backward
compatibility.  Although formally specifying the x86 ISA in its
entirety would be ideal, the focus of these books is the 64-bit
sub-mode of Intel's IA-32e mode --- most modern software relies on
64-bit computing anyway. Some components of the x86 ISA state that
need to be modeled are as follows:</p>

<ul>

<li>General-purpose registers \(e.g., @('rax'), @('rbx'), etc.\),
segment registers \(e.g., @('cs'), @('ss'), etc.\), machine-specific
registers \(e.g., @('ia32\_efer'), @('ia32\_fs\_base'), etc.\),
etc.</li>

<li>64-bit instruction pointer @('rip')</li>

<li>64-bit flags @('rflags')</li>

<li>Memory management registers \(e.g., @('ldtr'), @('gdtr')\)</li>

<li>Physical and linear memory address space</li>

</ul>

<p>Other capabilities that are supported include all the addressing
modes, memory management via paging and segmentation, and the
instruction fetch-decode-execute cycle.</p>

</li>

<li>
<b>Reasoning <i>and</i> Execution Efficiency:</b> <p>These books
contain a formal x86 ISA model that is not only capable of reasoning
about x86 machine-code programs, but also of simulating those
programs.  Reasoning efficiency is desirable to make code proofs
tractable \(and we need all the help we can get for performing code
proofs!\) and execution efficiency is desirable to enable faster model
validation via co-simulations \(See @(see model-validation) for
details.\).</p>

<p>However, simple definitions that are suitable for reasoning
typically offer poor execution performance and definitions optimized
for execution efficiency often use a sufficiently different algorithm
from the one used in the specification that they are difficult to
reason about.  However, ACL2 offers several features to mitigate this
trade-off between reasoning and execution efficiency.  For e.g.: @(see
mbe) and its friends like @(see acl2::mbt), and @(see acl2::assert*),
@(see acl2::stobj), and @(see acl2::defabsstobj).</p>

<p>ACL2 features like abstract stobjs and @('assert*') were a response
by the ACL2 authors to provide mechanisms to mitigate the complexity
of reasoning vs. execution efficiency that came up over the course of
this project.  This x86 ISA model uses abstract stobjs to layer the
state of the x86 machine such that the lower layer \(i.e., the
concrete stobj\, see @(see x86-concrete-state)\) can be optimized for
execution efficiency and the upper layer \(i.e., the abstract stobj,
see @(see x86-abstract-state)\) can be optimized for reasoning
efficiency, while a correspondence theorem is proved to hold between
these two layers at all times.  Therefore, we get the benefit of both
fast execution and effective reasoning.</p>
</li>

<li>

<b>Level of Reasoning:</b> <p>The complexity of the x86 ISA model will
increase as more features are added to it, and this added complexity
will make reasoning inevitably more involved.  The issue of balancing
<i>verification effort</i> and <i>verification utility</i> is a very
pertinent one.  For example, users might not want to reason about an
application program at the level of physical memory, i.e., taking into
account address translations and access rights management provided by
the memory management data structures.  This is because it is
customary for application programs not to have direct access to the
system data structures.  The memory model seen by application programs
is that of linear memory, which is an OS-constructed abstraction of
the complicated underlying memory management mechanisms like paging
and segmentation that are based on physical memory.  Therefore,
verification of application programs can be performed at the level of
linear memory, if the OS routines that manage the linear memory
abstraction can be either trusted or proved correct.  However, the
verification of system programs, like kernel routines, must
necessarily be done at the level of physical memory since these
programs can access/modify system data structures.</p>

<p>In light of the above, the x86 ISA model provides the option to
deactivate some features of the ISA, enabling the user to do two kinds
of analysis, depending on the kind of programs being considered for
verification.  Specifically, the x86 model has the following modes of
operation:</p>

<ol>

<li><b>Programmer-level Mode:</b> <p>This mode of the model attempts
to provide the same environment for reasoning as is provided by an OS
for programming.  It allows the verification of an application program
while assuming that memory management, I/O operations, and services
offered via system calls are provided reliably by the underlying OS.
The memory model in this mode supports 64-bit linear addresses
specified for IA-32e machines.  A specification of system calls like
@('read'), @('write'), @('open'), and @('close') is also included in
the programmer-level mode.</p></li>

<li><b>System-level Mode:</b> <p>This mode includes the specification
  for IA-32e paging and segmentation; in particular, ISA-prescribed
  data structures for memory management are available in this mode.
  The memory model in this mode characterizes a 52-bit physical
  address space, which is the largest physical address space provided
  by modern x86 implementations.  This mode is intended to be used to
  simulate and verify software that has supervisor privileges and
  interacts with I/O devices.</p> </li>

</ol>

<p>An added benefit of having two separate modes of operation is the
increased execution speed of programs in the programmer-level mode;
this is because executing these programs in this mode does not require
simulating both the physical address space \(and hence,
accesses/updates to the paging and segmentation data structures\) and
the linear address space.</p>

<p>It would be beneficial, not to mention interesting, to verify
whether the programmer-level mode is an abstraction of the
system-level mode, given that the system data structures have been set
up correctly.  As of now, establishing this relationship between the
two modes is out of the scope of this project.</p>

</li>

</ul>

")

(defxdoc model-validation
  :parents (x86isa)
  :short "How do we trust that our x86 ISA model is faithful to the
  real machine?"

  :long "<p>Doc topic coming soon!  For now, here's an illustrative
  image.</p>

<p><img src='res/x86-images/cosim.png' /></p>")

(defxdoc Publications
  :parents (x86isa)
  :short "Technical publications related to the work done during this project"
  :long "<ol>

<li>Warren A. Hunt, Jr. and Matt Kaufmann. Towards a Formal Model of
  the x86 ISA. Technical Report, Department of Computer Science, The
  University of Texas at Austin.</li>

<li>Warren A. Hunt, Jr. and Matt Kaufmann. A Formal Model of a Large
  Memory that Supports Efficient Execution. In Proceedings of the 12th
  International Conference on Formal Methods in Computer-Aided
  Design (FMCAD 2012, Cambrige, UK, October 22-25), 2012</li>

<li>Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann. Abstract
  Stobjs and Their Application to ISA Modeling. In Proceedings of the
  ACL2 Workshop 2013, EPTCS 114, pp. 54-69, 2013</li>

<li>Shilpi Goel and Warren A. Hunt, Jr. Automated Code Proofs on a
  Formal Model of the x86. In Verified Software: Theories, Tools,
  Experiments (VSTTE 13), volume 8164 of Lecture Notes in Computer
  Science, pages 222 241. Springer Berlin Heidelberg, 2014</li>

<li>Shilpi Goel, Warren A. Hunt, Jr., Matt Kaufmann, and Soumava
  Ghosh. Simulation and Formal Verification of x86 Machine-Code
  Programs That Make System Calls. In Proceedings of the 14th
  Conference on Formal Methods in Computer-Aided Design (FMCAD 14),
  pages 18:91 98, 2014</li>

</ol>")

(defxdoc Build-Instructions
  :parents (x86isa)
  :short "Building books related to the x86 ISA and the machine-code
  analysis framework"

  :long "<p>Two ways of building the X86ISA books are:</p>

<ol>

<li>
<p>Using the Makefile provided with the X86ISA books: Users of these
books who wish to simulate x86 programs with non-deterministic
computations like @('SYSCALL') \(in @(see programmer-level-mode)\) and
@('RDRAND') should use this Makefile and run make with
@('X86ISA_EXEC') set to @('t') \(which is the default value\).</p>

<code>
make JOBS=8 \\
     X86ISA_EXEC=t \\
     ACL2=/Users/shilpi/acl2/saved_acl2
</code>
<p>where the number of jobs to be run in parallel in this example is
8.  Note that we use @('JOBS') here instead of the @('-j') flag.</p>

<p>When @('X86ISA_EXEC') is @('t'), some dynamic C libraries that are
used in the model for supporting the execution of @('SYSCALL') in the
programmer-level mode and @('RDRAND') will be built.  <b>Since we rely
on the foreign function interface of <a
href='http://ccl.clozure.com/'>Clozure CL</a> (CCL), full execution
support is available only if you use CCL.</b></p>

<p>Values of @('X86ISA_EXEC') other than @('t') will not allow the
execution of @('SYSCALL') and @('RDRAND') instructions \(as may be the
case with using other Lisps as well\).  Note that reasoning about
these instructions will still be possible.  Execution and reasoning
about all other instructions will always be possible, irrespective of
@('X86ISA_EXEC') or the underlying Lisp.</p>

<p><b>IMPORTANT:</b> You should do a \"make clean\" \(or \"make
execclean\" if you are in a hurry\) if you wish to certify the books
with a different value of @('X86ISA_EXEC').</p>

</li>

<li> <p>Using the \"everything\" target of the ACL2 Community
Books (see acl2/books/GNUmakefile): This is essentially the same as
executing @('cert.pl books/projects/x86isa/top'). This will build the
x86 books without full execution support, i.e., the effect will be the
same as building these books with @('X86ISA_EXEC=nil'), even though
the Makefile provided with the X86ISA books will not be used.</p>
</li>

</ol>

<p>Suppose you had certified these books previously, but you have
since forgotten whether you built them with @('X86ISA_EXEC=t') or not.
Here is a way of checking the certified books to see if you have full
execution support. Look at the following file:
@('machine/x86-syscalls.cert.out'). If this file contains the
following: </p>

<code>X86ISA_EXEC Warning: x86-environment-and-syscalls-raw.lsp is not
included.</code>

<p>then you do <i>not</i> have @('SYSCALL') execution support.
Otherwise, you do. If, in @('machine/x86-other-non-det.cert.out'), you
find the following string, then you do <i>not</i> have @('RDRAND')
execution support, either because the books were certified with
@('X86ISA_EXEC') not equal to @('t') or because your processor does
not support the @('RDRAND') instruction:</p>

<code>X86ISA_EXEC Warning: x86-other-non-det-raw.lsp is not
included.</code>
"
  )

(defxdoc Contributors
  :parents (x86isa)
  :short "Authorship Details and Acknowledgements"
  :long "<h5>Original Authors</h5>
<p>Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann</p>

<p>Questions or Suggestions? Email Shilpi:
<tt>shigoel@cs.utexas.edu</tt></p>

<p>This material is based upon work supported by DARPA under Contract
  No. N66001-10-2-4087.</p>

<h5>Contributors to the x86 ISA Model</h5>

<p>Thanks to Cuong Kim Chau for implementing some floating point
instructions and for performing many experiments \(along with Keshav
Kini\) to figure out an efficient configuration for the concrete
memory model.</p>

<p>Thanks to Soumava Ghosh for his work on supporting the execution of
system calls and the ELF loader functions.</p>

<p>Thanks to Keshav Kini for answering all sorts of git-related
questions and for performing many experiments \(along with Cuong Kim
Chau\) to figure out an efficient configuration for the concrete
memory model.</p>

<p>Thanks to Robert Krug for carrying out countless arithmetic proofs,
and for the initial specification of the paging mechanism and proofs
about properties of paging data structures.</p>

<p>Thanks to Ben Selfridge for putting in type declarations and
resolving the resulting guard proof obligations about the paging
specification functions.</p>

<h5>Acknowledgements</h5>

<p>Thanks to the folks at <a href=\"http://www.centtech.com\">Centaur
Technology</a> \(Anna Slobodova, Jared Davis, and Sol Swords\) for
their suggestions and their wonderful libraries, especially the
@('bitops') books.</p>

<p>Thanks to Marijn Heule for contributing his SAT solver for model
validation.</p>

<p>Thanks to J Moore for too many things to count.</p>

<p>Thanks to Nathan Wetzler for helpful discussions, especially on
  proving properties of paging data structures.</p>" )

(defxdoc TO-DO
  :parents (x86isa)
  :short "Known issues, planned activities, wishlists, etc."
  :long "<ol>

<li><b>To-do:</b> Check the segmentation specification and test the
far @('jmp') instruction.</li>

<li><b>To-do:</b> Speed up
proofs/utilities/x86-row-wow-thms.lisp.</li>

<li><b>To-do:</b> Resolve name conflicts in the factorial proof
books.</li>

<li><b>To-do:</b> Generate the dispatch function using
implemented-opcodes-table in machine/x86.lisp.  Sort
implemented-opcodes-table on the opcode at least, if not also the
opcode extensions.</li>

<li><b>To-do:</b> Verify guards of functions in
tools/execution/exec-loaders/elf.</li>

<li><b>Someday maybe:</b> Save memory by loading either the elf or
mach-o stobj as necessary, as opposed to loading both by default in
tools/execution/top.lisp.</li>

</ol>"

  )

(defun print-implemented-opcodes-table (op-table)
  (declare (xargs :mode :program))
  ;; (print-implemented-opcodes-table (table-alist 'implemented-opcodes-table (w state)))
  (if (endp op-table)
      ""
    (b* ((t-entry           (car op-table))
         (ins-name          (car (cdr t-entry)))
         (semantic-fn-name  (cdr (cdr t-entry)))
         (t-opcode-info     (car t-entry))
         (t-opcode          (car t-opcode-info))
         (opcode-string     (cond
                             ((n04p t-opcode)
                              (string-append "0" (str::natstr16 t-opcode)))
                             ((n08p t-opcode)
                              (str::natstr16 t-opcode))
                             ((n12p t-opcode)
                              (string-append "0" (str::natstr16 t-opcode)))
                             (t
                              (str::natstr16 t-opcode))))
         (opcode-extns      (cdr t-opcode-info))
         (opcode-extns      (if (equal (car opcode-extns) :nil)
                                'NONE
                              opcode-extns))

         (table-info-string
          (fms-to-string
           "Opcode: ~s0 Extension: ~y1 ~t3 Instruction: ~s2~%~t3 Semantic Function: ~s4~%~%"
           (list (cons #\0 opcode-string)
                 (cons #\1 opcode-extns)
                 (cons #\2 ins-name)
                 (cons #\3 '8)
                 (cons #\4 semantic-fn-name)))))
        (string-append
         table-info-string
         (print-implemented-opcodes-table (cdr op-table))))))

(defsection implemented-opcodes
  :parents (x86-instructions)
  :short "Opcodes supported by the x86 model"
  :long "<p><b>TO-DO:</b> The following list is not sorted on opcodes
  yet.</p>

 @(`
   (:code (print-implemented-opcodes-table
           (reverse
            (table-alist 'implemented-opcodes-table (w state)))))
`)

")

(xdoc::order-subtopics
 x86-instructions
 (implemented-opcodes
  x86-instruction-semantics
  one-byte-opcodes
  two-byte-opcodes
  fp-opcodes
  privileged-opcodes))

(xdoc::order-subtopics
 machine
 (x86-concrete-state
  x86-concrete-memory
  x86-abstract-state
  x86-state-field-theorems
  programmer-level-mode
  rflag-specifications
  x86-register-readers-and-writers
  Characterizing-undefined-behavior
  x86-physical-memory
  ia32e-paging
  ia32e-segmentation
  x86-top-level-memory
  x86-environment
  x86-syscalls
  other-non-deterministic-computations
  x86-decoding-and-spec-utils
  x86-instructions
  x86-decoder))

;; ======================================================================
