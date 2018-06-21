;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; x86 ISA model specification
(include-book "machine/x86" :ttags :all)

;; Misc. tools
(include-book "tools/execution/top" :ttags :all)

;; General-purpose code libraries: note that we don't include
;; proofs/top here --- the proofs of correctness of various programs
;; are excluded from the x86isa manual.
(include-book "proofs/utilities/top" :ttags :all)
(include-book "std/strings/top" :dir :system)
(include-book "defsort/defsort" :dir :system)

;; ======================================================================

;; Files will be copied from X86ISA/images to res/images of the x86
;; manual.
(xdoc::add-resource-directory "images" "images")

(defxdoc X86ISA
  :parents (acl2::software-verification acl2::projects)
  :short "x86 ISA model and machine-code analysis framework developed
  at UT Austin"
  :long "<p><img src='res/images/x86isa.png' /></p>")

(xdoc::order-subtopics
 X86ISA
 (Introduction
  x86isa-build-instructions
  utils
  machine
  program-execution
  model-validation
  proof-utilities
  debugging-code-proofs
  Contributors
  Publications
  TO-DO
  LICENSE))

(defsection Introduction
  :parents (x86isa)

  :short "A Formal and Executable Model of the x86 Instruction Set Architecture"

  :long "<p>These books contain the specification of x86 instruction
 set architecture \(ISA\); we characterize x86 machine instructions and
 model the instruction fetch, decode, and execute process using the
 ACL2 theorem-proving system.  We use our x86 ISA specification to
 formally verify x86 machine-code programs.</p>

 <p>These books include:</p>

 <ul>

 <li>A formal, executable x86 ISA model \(see @('machine')
 sub-directory\)</li>

 <li>General theorems to aid in machine-code verification \(see
 @('proofs/utilities') sub-directory\)</li>

 <li>Examples of using these books to verify some programs \(see
  @('proofs') sub-directory\)</li>

 </ul>

 <p>For information on how to certify these books, see @(see
 x86isa-build-instructions).</p>

 <h3>Completeness of the x86 Model</h3>

 <p>The utility of a formal ISA model for performing machine-code
 verification depends directly on the model's completeness \(with
 respect to the ISA features specified\), accuracy, and reasoning and
 execution efficiency.  <a
 href='http://www.intel.com/content/www/us/en/processors/architectures-software-developer-manuals.html'>Intel
 software developer's manuals</a> were used as specification documents,
 and ambiguities were resolved by cross-referencing <a
 href='http://developer.amd.com/resources/documentation-articles/developer-guides-manuals/'>AMD
 manuals</a> and running tests on real machines to understand processor
 behavior.  </p>

 <p>There are a multitude of features in the x86 ISA that include those
 left over from its early days to ensure backward
 compatibility. Although formally specifying the x86 ISA in its
 entirety would be ideal, the focus of these books is the <b>64-bit
 sub-mode of Intel's IA-32e mode</b> --- most modern software relies on
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

 <p>The model is being extended to support 32-bit mode, both as the legacy
 protected mode and as the compatibility sub-mode of Intel's IA-32e mode.  This
 extension is still experimental; it has not been thoroughly tested yet.</p>

 <p>To see a list of opcodes implemented in these books, see @(see
 implemented-opcodes).</p>

 <h3>Reasoning and Execution Efficiency</h3>

 <p>These books contain a formal x86 ISA model that is not only
 capable of reasoning about x86 machine-code programs, but also of
 simulating those programs. See @(see program-execution) for
 instructions on how to set up the @('x86isa') model for executing a
 program.</p>

 <p>Reasoning efficiency is desirable to make code proofs tractable
 and execution efficiency is desirable to enable faster model
 validation via co-simulations \(See @(see model-validation)\).</p>

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
 concrete stobj\, see @(see concrete-state)\) can be optimized for
 execution efficiency and the upper layer \(i.e., the abstract stobj,
 see @(see abstract-state)\) can be optimized for reasoning
 efficiency, while a correspondence theorem is proved to hold between
 these two layers at all times.  Therefore, we get the benefit of both
 fast execution and effective reasoning.</p>

 <h3>Modes of Operation</h3>

 <p>The complexity of the x86 ISA model will increase as more features are
 added to it, and this added complexity will make reasoning inevitably more
 involved.  The issue of balancing <i>verification effort</i> and
 <i>verification utility</i> is a very pertinent one.  For example, users might
 not want to reason about an application program at the level of physical
 memory, i.e., taking into account address translations and access rights
 management provided by the memory management data structures.  This is because
 it is customary for application programs not to have direct access to the
 system data structures.  The memory model seen by 64-bit application programs
 is that of linear memory, which is an OS-constructed abstraction of the
 complicated underlying memory management mechanisms like paging that are based
 on physical memory.  Therefore, verification of application programs can be
 performed at the level of linear memory, if the OS routines that manage the
 linear memory abstraction can be either trusted or proved correct.  However,
 the verification of system programs, like kernel routines, must necessarily be
 done at the level of physical memory since these programs can access/modify
 system data structures.</p>

 <p>In light of the above, the x86 ISA model provides the option to
 deactivate some features of the ISA, enabling the user to do two
 kinds of analysis, depending on the kind of programs being considered
 for verification.  Specifically, the model offers the following views
 of x86 machines:</p>

 <ol>

 <li><b>Application-Level View:</b> <p>In this view, the model
 attempts to provide the same environment for reasoning as is provided
 by an OS for programming.  It allows the verification of an
 application program while assuming that memory management, I/O
 operations, and services offered via system calls are provided
 reliably by the underlying OS.  The memory model here supports 64-bit
 linear addresses specified for IA-32e machines.  A specification of
 system calls like @('read'), @('write'), @('open'), and @('close') is
 also included in this view.</p></li>

 <li><b>System-level View:</b> <p>This view includes the specification
 for IA-32e paging and segmentation; in particular, ISA-prescribed
 data structures for memory management and (partial) specifications of
 system-mode instructions like LLDT and LGDT are available in this
 mode.  The memory model here characterizes a 52-bit physical address
 space, which is the largest physical address space provided by modern
 x86 implementations.  This view is intended to be used to simulate
 and verify software that has supervisor privileges and interacts with
 I/O devices.</p> </li>

 </ol>

 <p>An added benefit of having these two separate views is the
 increased execution speed of programs in the application-level view;
 this is because executing these programs in this view does not
 require simulating both the physical address space \(and hence,
 accesses/updates to the paging data structures\) and the linear
 address space.</p>

 <p>It would be beneficial, not to mention interesting, to verify
 whether the application-level view is an abstraction of the
 system-level view, given that the system data structures have been set
 up correctly.  As of now, establishing this relationship between the
 two modes is out of the scope of this project.</p>")

(defxdoc x86isa-build-instructions
  :parents (x86isa)
  :short "Building books related to the x86 ISA and the machine-code
  analysis framework"

  :long "<p>Two ways of building the @('x86isa') books are:</p>

 <ol>

 <li>
 <p>Using the Makefile provided with the @('x86isa') books: Users of
 these books who wish to simulate x86 programs with non-deterministic
 computations like @('SYSCALL') \(in @(see app-view)\)
 should use this Makefile and run make with @('X86ISA_EXEC') set to
 @('t') \(which is the default value\).</p>

 <code>
 make JOBS=8 \\
      X86ISA_EXEC=t \\
      ACL2=/Users/shilpi/acl2/saved_acl2
 </code>
 <p>where the number of jobs to be run in parallel in this example is
 8.  Note that we use @('JOBS') here instead of the @('-j') flag.</p>

 <p>When @('X86ISA_EXEC') is @('t'), some dynamic C libraries that are
 used in the model for supporting the execution of @('SYSCALL') in the
 application-level view will be built.  <b>Since we rely on the foreign
 function interface of <a href='http://ccl.clozure.com/'>Clozure
 CL</a> (CCL), full execution support is available only if you use
 CCL.</b></p>

 <p>Values of @('X86ISA_EXEC') other than @('t') will not allow the
 execution of @('SYSCALL') instructions \(as may be the case with
 using other Lisps as well\).  Note that reasoning about these
 instructions will still be possible.  Execution and reasoning about
 all other instructions will always be possible, irrespective of
 @('X86ISA_EXEC') or the underlying Lisp.</p>

 <p><b>IMPORTANT:</b> You should do a \"make clean\" \(or \"make
 execclean\" if you are in a hurry\) if you wish to certify the books
 with a different value of @('X86ISA_EXEC').</p>

 </li>

 <li> <p>Using the \"everything\" target of the ACL2 Community
 Books (see acl2/books/GNUmakefile): This is essentially the same as
 executing @('cert.pl books/projects/x86isa/top'). This will build the
 x86 books without full execution support, i.e., the effect will be
 the same as building these books with @('X86ISA_EXEC=nil'), even
 though the Makefile provided with the @('x86isa') books will not be
 used.</p> </li>

 </ol>

 <p>Suppose you had certified these books previously, but you have
 since forgotten whether you built them with @('X86ISA_EXEC=t') or not.
 Here is a way of checking the certified books to see if you have full
 execution support. Look at the following file:
 @('machine/syscalls.cert.out'). If this file contains the
 following: </p>

 <code>X86ISA_EXEC Warning: environment-and-syscalls-raw.lsp is not
 included.</code>

 <p>then you do <i>not</i> have @('SYSCALL') execution support.
 Otherwise, you do.</p>"
  )

(defxdoc model-validation
  :parents (x86isa)
  :short "How do we trust that our x86 ISA model is faithful to the
  real machine?"

  :long "<p>Doc topic coming soon!  For now, here's an illustrative
  image.</p>

<p><img src='res/images/cosim.png' /></p>")

(defxdoc Publications
  :parents (x86isa)
  :short "Technical publications related to the work done during this project"
  :long "<p>From the oldest to the newest:</p>
 <ol>

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

 <li>Shilpi Goel. Formal Verification of Application and System
  Programs Based on a Validated x86 ISA Model. Ph.D. Dissertation,
  Department of Computer Science, The University of Texas at
  Austin. 2016</li>

 <li>Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann.  Engineering
  a Formal, Executable x86 ISA Simulator for Software Verification. In
  Provably Correct Systems (ProCoS), 2017</li>

 <li>Shilpi Goel. The @('x86isa') Books: Features, Usage, and Future
  Plans. In the Fourteenth International Workshop on the ACL2 Theorem
  Prover and Its Applications (ACL2 Workshop), 2017</li>

 </ol>")

(defxdoc Contributors
  :parents (x86isa)
  :short "Authorship Details and Acknowledgments"
  :long "<h5>Original Authors</h5>
 <p>Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann</p>

 <p>Questions or Suggestions? Email Shilpi:
 <tt>shigoel@cs.utexas.edu</tt></p>

 <h5>Contributors to the x86 ISA Model</h5>

 <p>Thanks to Alessandro Coglio (Kestrel Institute and Kestrel Technology LLC)
 for adding growing support for 32-bit mode and for improving the documentation
 of these books.</p>

 <p>Thanks to Cuong Kim Chau for implementing the floating point
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

 <h5>Acknowledgments</h5>

 <p>This material is based upon work supported by DARPA under Contract
   No. N66001-10-2-4087.</p>

 <p>This material is based upon work supported by the National Science
  Foundation under Grant Number CNS-1525472.</p>

 <p>Thanks to the folks at <a href=\"http://www.centtech.com\">Centaur
 Technology</a> \(Anna Slobodova, Jared Davis, and Sol Swords\) for
 their suggestions and their wonderful libraries, especially the
 @('bitops') books.</p>

 <p>Thanks to Marijn Heule for contributing his SAT solver for model
 validation.</p>

 <p>Thanks to J Moore for too many things to count.</p>

 <p>Thanks to Nathan Wetzler for helpful discussions, especially on
   proving properties of paging data structures.</p>

 <p>Thanks to Arjen van Lith for designing the @('x86isa') logo.</p>"
 )

(defxdoc TO-DO
  :parents (x86isa)
  :short "Known issues, planned activities, wishlists, etc."

  :long "<p>If anyone is interested in carrying out the tasks or
  activities below, please feel free to contact Shilpi
  \(@('shigoel@cs.utexas.edu')\).</p>

 <h3>TO-DO</h3>

 <ul>

 <li>Remove the capability of reading and writing 6 and 10 bytes from
 @('x86-operand-*') functions, in light of alignment checking.</li>

 <li>Check the segmentation specification and test the far @('jmp')
 instruction.</li>

 <li>Verify guards of functions in
 @('tools/execution/exec-loaders/elf/').</li>

 </ul>

 <h3>Wishlist</h3>

 <ul>

 <li>Generate the dispatch function using
 @('implemented-opcodes-table') in @('machine/x86.lisp').</li>

 <li>Save memory by loading either the elf or mach-o stobj as
 necessary, as opposed to loading both by default in
 @('tools/execution/top.lisp').</li>

 </ul>")

(defxdoc LICENSE
  :parents (x86isa)

  :short "Copyright Information for the @('X86ISA') Library"

  :long "<p>Authors: Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann</p>

 <p>Note: The license below is based on the template at:
 <tt>http://opensource.org/licenses/BSD-3-Clause</tt></p>

 <p>Copyright (C) 2015, Regents of the University of Texas<br/>
 All rights reserved.</p>

 <p>Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are
 met:</p>

 <ul>

 <li> Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer. </li>

 <li> Redistributions in binary form must reproduce the above
   copyright notice, this list of conditions and the following
   disclaimer in the documentation and/or other materials provided
   with the distribution.</li>

 <li> Neither the name of the University of Texas, Austin nor the
   names of its contributors may be used to endorse or promote
   products derived from this software without specific prior written
   permission. </li>

 </ul>

 <tt>THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 \"AS IS\" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.</tt>"
  )

(defun implemented-opcodes-table-entry-p (e)
  (declare (xargs :guard t))
  ;; Maybe extend this to other fields too?
  (and (consp e)
       (consp (car e))
       ;; Opcode
       (natp (caar e))))

(defun implemented-opcodes-table-alist-p (l)
  (declare (xargs :guard t))
  (cond ((not (consp l)) (eq l nil))
        (t (and (implemented-opcodes-table-entry-p (car l))
                (implemented-opcodes-table-alist-p (cdr l))))))

(assert-event
 (equal (implemented-opcodes-table-alist-p
         (table-alist 'implemented-opcodes-table (w state)))
        t))

(defun x86-opcode-< (x y)
  (declare (xargs :guard (and (implemented-opcodes-table-entry-p x)
                              (implemented-opcodes-table-entry-p y))))
  (b* ((x-opcode (caar x))
       (y-opcode (caar y)))
    (< x-opcode y-opcode)))

(acl2::defsort sort-by-x86-opcodes<
               :prefix x86-sort-by-opcode
               :compare< x86-opcode-<
               :comparablep implemented-opcodes-table-entry-p
               :comparable-listp implemented-opcodes-table-alist-p
               :true-listp t
               :weak t)

;; (sort-by-x86-opcodes< (table-alist 'implemented-opcodes-table (w state)))

(defun print-implemented-opcodes-table (op-table)
  (declare (xargs :mode :program))
  ;; (print-implemented-opcodes-table (table-alist 'implemented-opcodes-table (w state)))
  (if (endp op-table)
      nil
    (b* ((t-entry           (car op-table))
         (ins-name          (symbol-name (car (cdr t-entry))))
         (semantic-fn-name  (symbol-name (cdr (cdr t-entry))))
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
                                nil
                              opcode-extns))

         (table-info-string
          (fms-to-string
           "<li>Opcode: ~s0 Extension: ~y1 Mnemonic: <b>~s2</b> <br/> Semantic Function: @(see ~s3)</li>"
           (list (cons #\0 opcode-string)
                 (cons #\1 opcode-extns)
                 (cons #\2 ins-name)
                 (cons #\3 semantic-fn-name)))))
      (concatenate
       'string
       table-info-string
       (print-implemented-opcodes-table (cdr op-table))))))

(define generate-implemented-opcodes-section (state)
  :mode :program
  ;; TO-DO: Link to relevant sections in the Intel manuals?
  (b* ((long-section
        (string-append-lst
         (list
          "<p>In the list below, <i>opcode</i> refers to the x86
  opcode (one- or two-byte) in hexadecimal, <i>extension</i> refers to
  the opcode extension (e.g., an implementation of the CMP instruction
  is identified by both the opcode 0x80 and the extension 3, which is
  the value of the REG field in the ModR/M byte of the instruction),
  <i>mnemonic</i> refers to the name of the instruction, and
  <i>semantic function</i> refers to the specification function of
  that opcode in the <tt>x86isa</tt> books.</p>

  <ul>"
          (print-implemented-opcodes-table
           (sort-by-x86-opcodes< (table-alist 'implemented-opcodes-table (w state))))

          "</ul>"))))

    `(defsection implemented-opcodes
       :parents (instructions)
       :short "Opcodes supported by the x86 model"
       :long ,long-section)))

(make-event (generate-implemented-opcodes-section state))

(xdoc::order-subtopics
 instructions
 (implemented-opcodes
  instruction-semantic-functions
  one-byte-opcodes
  two-byte-opcodes
  fp-opcodes
  privileged-opcodes))

(xdoc::order-subtopics
 machine
 (concrete-state
  concrete-memory
  abstract-state
  state-field-theorems
  app-view
  rflag-specifications
  register-readers-and-writers
  characterizing-undefined-behavior
  physical-memory
  linear-memory
  paging
  segmentation
  top-level-memory
  environment
  syscalls
  other-non-deterministic-computations
  decoding-and-spec-utils
  instructions
  x86-decoder))

;; ======================================================================
