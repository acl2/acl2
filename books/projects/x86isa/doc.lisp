; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2024 Intel Corporation

; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; x86 ISA model specification
(include-book "machine/x86" :ttags :all)
(include-book "machine/inst-listing" :ttags :all)

;; Misc. tools
(include-book "tools/execution/top" :ttags :all)
;; Examples of concrete simulations
(include-book "tools/execution/examples/top" :ttags :all)


;; General-purpose code libraries: note that we don't include
;; proofs/top here --- the proofs of correctness of various programs
;; are excluded from the x86isa manual.
(include-book "proofs/utilities/top" :ttags :all)

;; Virtualization based validation
(include-book "virtualization/top" :ttags :all)

;; Saving and restoring the state
(include-book "machine/save-restore" :ttags :all)

;; ======================================================================

;; Files will be copied from X86ISA/images to res/x86isa of the x86
;; manual. Note: this needs to be replicated in projects/top-doc (with path corrected).
(xdoc::add-resource-directory "x86isa" "images")

; (depends-on "images/x86isa.png")

(defxdoc X86ISA
  :parents (acl2::software-verification acl2::hardware-verification acl2::projects)
  :short "x86 ISA model and machine-code analysis framework developed
  at UT Austin."
  :long "<p><img src='res/x86isa/x86isa.png' /></p>")

(defsection introduction
  :parents (x86isa)

  :short "A formal and executable model of the x86 Instruction Set
  Architecture."

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
 href='https://developer.amd.com/resources/developer-guides-manuals/'>AMD
 manuals</a> and running tests on real machines to understand processor
 behavior. </p>

 <p>The current focus of these books is Intel's <b>IA-32e mode</b>, which
 includes 64-bit and Compatibility sub-modes, and the <b>32-bit protected
 mode</b>.</p>

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
 validation via co-simulations \(see @(see model-validation)\).</p>

 <p>However, simple definitions that are suitable for reasoning
 typically offer poor execution performance and definitions optimized
 for execution efficiency often use a sufficiently different algorithm
 from the one used in the specification that they are difficult to
 reason about.  However, ACL2 offers several features to mitigate this
 trade-off between reasoning and execution efficiency.  For e.g.: @(see
 mbe) and its friends like @(see acl2::mbt), and @(see acl2::assert*),
 @(see acl2::stobj), and @(see acl2::defabsstobj).</p>

 <p>ACL2 features like abstract stobjs and @('assert*') were a
 response by the ACL2 authors to provide mechanisms to mitigate the
 complexity of reasoning vs. execution efficiency that came up over
 the course of this project.  This x86 ISA model uses abstract stobjs
 to layer the state of the x86 machine such that the lower layer
 \(i.e., the concrete stobj\) can be optimized for execution
 efficiency and the upper layer \(i.e., the abstract stobj) can be
 optimized for reasoning efficiency, while a correspondence theorem is
 proved to hold between these two layers at all times.  Therefore, we
 get the benefit of both fast execution and effective reasoning.</p>

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
  analysis framework."

  :long "<p>Some ways of building the @('x86isa') books are:</p>

 <ol>

 <li>
 <p>Using @('cert.pl top'): This @(see build::cert.pl) option should work well
 for most users.  Users who want to execute programs that utilize @('SYSCALL'),
 @('RDRAND'), etc. should consider the option listed below.</p>
 </li>

 <li>
 <p>Using the Makefile provided with the @('x86isa') books: Users of these
 books who wish to simulate x86 programs with non-deterministic computations
 like @('SYSCALL') \(in @(see app-view)\) should use the Makefile provided with
 @('x86isa') and run make with @('X86ISA_EXEC') set to @('t') \(which is the
 default value\).</p>

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

; (depends-on "images/cosim.png")

(defxdoc model-validation
  :parents (x86isa)
  :short "How do we trust that our x86 ISA model is faithful to the
  real machine?"

  :long "<p>A past version of this model was validated in @('app-view') with
  cosimulation using tools internal to Centaur Technology. See the graphic bellow:</p>

 <p><img src='res/x86isa/cosim.png' /></p>

 <p>This validation system was lost to history. To debug the model while
 attempting to boot Linux on it, we built a new validation system that works
 similarly, but works in the @('system-view') and is built on opensource tools.
 For more information see @(see virtualization-for-validation)</p>")

(defxdoc publications
  :parents (x86isa)
  :short "Technical publications related to these @('x86isa') books."
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

 <li>Alessandro Coglio and Shilpi Goel. Adding 32-bit Mode to the ACL2 Model of
  the x86 ISA. In the Fifteenth International Workshop on the ACL2 Theorem
  Prover and Its Applications (ACL2 Workshop), 2018</li>

 <li>Shilpi Goel and Rob Sumners. Using @('x86isa') for Microcode
 Verification. In the Workshop on Instruction Set Architecture
 Specification (SpISA), 2019.</li>

 <li>Shilpi Goel, Anna Slobodova, Rob Sumners, and Sol
 Swords. Verifying x86 Instruction Implementations. In the proceedings
 of the 9th ACM SIGPLAN International Conference on Certified Programs
 and Proofs (CPP), 2020.</li>

 </ol>")

(defxdoc contributors
  :parents (x86isa)
  :short "Authorship details and acknowledgments."
  :long "<h5>Original Authors</h5>
 <p>Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann</p>

 <p>Questions or Suggestions? Email Shilpi:
 <tt>shigoel@gmail.com</tt>.</p>

 <h5>Contributors to the x86 ISA Model</h5>

 <p>Thanks to Rob Sumners for adding support for detecting decode-time
 exceptions.</p>

 <p>Thanks to Alessandro Coglio (Kestrel Institute and Kestrel Technology LLC)
 for adding support for 32-bit mode and for improving the documentation of
 these books.</p>

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

 <p>Thanks to folks formerly at Centaur Technology \(including Anna Slobodova,
 Jared Davis, and Sol Swords\) for their suggestions and their wonderful
 libraries, especially the @('bitops') books.</p>

 <p>Thanks to Marijn Heule for contributing his SAT solver for model
 validation.</p>

 <p>Thanks to J Moore for too many things to count.</p>

 <p>Thanks to Nathan Wetzler for helpful discussions, especially on
   proving properties of paging data structures.</p>

 <p>Thanks to Arjen van Lith for designing the @('x86isa') logo.</p>"
 )

(defxdoc to-do
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

 <li>Add support for handling more exceptions. In the past, no exception
 handling was supported. In the effort to boot Linux, we added support for page
 faults, but most other exceptions are still unhandled.</li>

 </ul>

 <h3>Wishlist</h3>

 <ul>

 <li>Save memory by loading either the elf or mach-o stobj as
 necessary, as opposed to loading both by default in
 @('tools/execution/top.lisp').</li>

 </ul>")

(defxdoc booting-linux
         :parents (x86isa)
         :short "Booting linux on the @('x86isa') model."

         :long "<p>The x86isa model is capable of booting a slightly modified
         version of Linux. This version of Linux is modified to add support for
         our timer and TTY devices and a few other minor changes.</p>

         <p>The following is a guide explaining how to boot Linux. First we
         build the modified kernel. Then, we setup a root filesystem for the
         machine running under the model. Finally, we load these into the model
         and execute it.</p>

         <h3>Building the Modified Kernel</h3>
         <p>Rather than distributing the entire modified kernel source tree,
         we've chosen to distribute a patch. We will download and patch the
         Linux source tree via git. First, clone the Linux source tree from
         kernel.org.</p>

         <code>
         git clone https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
         cd linux
         </code>

         <p>This will clone the Linux source tree into a folder called
         @('linux') in your current working directory and then @('cd') into it.
         We hope our patch continues to work on newer kernels, and welcome
         contributions to fix it if it doesn't, but it was last tested applied
         to commit @('12214540ad87'). If you wish to use this version, which is
         what I recommend if you don't wish to deal with merge conflicts, run
         the following command:</p>

         <code>
         git checkout 12214540ad87
         </code>

         <p>Now, we must apply the patch. The patch file is found in the ACL2
         source tree in the file @('books/projects/x86isa/linux/x86isa-linux.patch').
         Run the following command to apply it:</p>

         <code>
         git apply &lt;path to patch file&gt;
         </code>

         <p>All that's left to do is build the kernel. Normally, at this point
         you'd run @('make menuconfig') to configure the kernel, but we
         included a @('.config') file in the patch that configures the kernel
         to work with the @('x86isa') model, so you don't need to do that.
         Thus, all we have left to do is build the kernel.</p>

         <p>Linux supports GCC and LLVM. I'm using @('gcc') version 13.2.0, but
         I expect other versions of GCC will work fine. LLVM has not been
         tested, but I'd expect it to work too. Follow the usual LLVM Linux
         compilation steps if you wish to try that.</p>

         <p>To compile with GCC, run:</p>
         <code>
         make
         </code>

         <p>Using multiple cores can increase build speed. Use</p>
         <code>
         make -j
         </code>
         <p>or</p>
         <code>
         make -j&lt;nprocs&gt;
         </code>
         <p>to use as many threads as you have logical processors or
         @('<nprocs>') threads to build respectively.</p>

         <p>This will build a @('bzImage') in @('arch/x86/boot/bzImage'). This
         is the file we will load into the model.</p>

         <h3>Setting up a Root Filesystem</h3>
         <p>Note: you'll probably need a Unix like system for this step because
         we deal with Unix device files. In principle, there's no reason why we
         have to actually create these files in our filesystem and can't
         directly construct the cpio archive containing them, but I don't know
         of any tools to do that. If you're on Windows, using WSL is an option.
         Once you make the rootfs image, you can transfer it to whatever system
         you wish to use.</p>

         <p>Most modern Linux machines boot by first loading an initramfs as
         the filesystem mounted on @('/'). This, as the name suggests, is an
         initial filesystem which resides in RAM. The kernel then starts
         @('/init'), which mounts the \"real\" root filesystem, usually from a
         disk. Then it uses the @('pivot_root') syscall to make it the new
         @('/'). This allows Linux to dynamicly link in the appropriate kernel
         modules from the initramfs, including disk and filesystem drivers
         necessary to mount the \"real\" disk.</p>

         <p>On our machine, we choose to use the initramfs as our root
         filesystem and don't @('pivot_root'). This makes it so that we don't
         have to use a disk device to boot. Linux requires the initramfs to be
         a gzip compressed @('cpio') archive.</p>

         <p>While this should work with other Linux distributions, we've tested
         the model with Alpine Linux's rootfs. We chose this distribution
         because it is small, making it easy to quickly recreate the cpio
         archive as needed when testing and because they provide a download
         link on their website for a tarball of their rootfs, rather than
         having to bootstrap the rootfs using a tool like Arch Linux's
         @('pacstrap').</p>

         <p>Alpine Linux's rootfs can be downloaded here:
         https://alpinelinux.org/downloads/ under the heading \"Mini Root
         Filesystem\". You want the one built for @('x86_64'). This has been
         tested with Alpine Linux version 3.20.2 but I expect newer versions to
         work fine too.</p>

         <p>Once you've downloded the Alpine mini root filesystem, do the
         following to extract it:</p>

         <code>
         mkdir alpine
         cd alpine
         # Note: the Alpine tarball will extract into your current directory,
         # so you should create a directory to contain the files, as shown
         # above
         tar xvf &lt;downloaded Alpine tarball path&gt;
         </code>

         <p>Now, we create the @('/dev/console') device file. Creating this file
         requires root. In theory, It should be possible to create a cpio
         archive containing this file without root. However, the @('cpio') tool
         creates a cpio archive out of files on the filesystem. If you don't
         have root on the machine you want to run the model on, you can always
         create the initramfs on another computer and transfer it to the machine
         you intend to boot Linux on.</p>

         <p>Run the following command (in the directory you extracted the Alpine
         rootfs to) to create the @('/dev/console') device file.</p>
         <code>
         sudo mknod dev/console c 5 3
         </code>

         <p>Next, we need to add a @('/init') executable. On Linux and other
         Unix like systems, @('/init') is the first program the kernel starts
         once it's done booting, and it runs until the system is shutdown. All
         processes are children of @('/init') and forked from it or one of its
         descendants.</p>

         <p>Any executable you wish to run on the model that works with Alpine
         Linux will work. We wish to start @('/bin/sh'). On many systems, one
         could simply symlink @('/init') to @('/bin/sh'), but we can't do that
         on Alpine Linux because Alpine uses Busybox's implementation of @('sh')
         (as opposed to the more common Dash or GNU Bash implementation).</p>

         <p>Busybox is an implementation the standard complement of utilities
         you'd expect to find on Unix like systems, including @('sh'), @('ls'),
         @('mount'), etc., kind of like GNU Coreutils. It is meant to be
         lightweight and is common in embedded systems. For this reason, Busybox
         is compiles all these tools into a single @('busybox') executable. If
         you inspect to contents of @('bin') in your Alpine rootfs, you'll
         notice that most executables are symlinks to @('/bin/busybox').</p>

         <p>When started, Busybox inspects the contents of @('argv[0]') to
         determine which program it should behave like. Thus, the same binary
         acts like @('ls') when it is called using the @('ls') symlink and acts
         like @('sh') when it is called with the @('ls') symlink. If we symlink
         @('/init') to @('/bin/sh') Busybox will be started with @('argv[0]') =
         to @('/init'), so it won't know that we want it to behave like
         @('sh').</p>

         <p>The solution for this is to write a little program which starts
         @('sh'). There is however a complication here too. Alpine uses musl as
         its implementation of libc and not GNU's glibc, which most Linux
         systems use. Thus, if you simply compile a dynamicly linked C program
         on a glibc Linux machines and try to run it on an Alpine Linux system,
         it won't run since it won't be able to find glibc.</p>

         <p>Therefore, we can either setup a musl toolchain and compile with a
         compatible version of musl or build a statically linked executable. I
         choose to use a statically linked executable, mainly since I didn't
         want to setup a musl toolchain, and since I don't want to link in all
         of glibc, I wrote it in assembly.</p>

         <p>You can find the program in
         @('books/projects/x86isa/linux/hello-user.S') in the ACL2 source tree.
         This program simply writes 'hello from userspace' to stdout and then
         @('execve')s @('/bin/sh'), replacing itself with the shell. It is
         meant to be assembled with the Netwide Assembler (NASM), which can be
         found at https://www.nasm.us/. Once you have it installed, run the
         following at the shell to assemble and then link it (the linking
         mainly just converts the object file to an executable, since we aren't
         linking anything else into the binary):</p>
         <code>
         nasm -f elf64 hello-user.S
         ld hello-user.o -o hello-user
         </code>

         <p>Then copy the @('hello-user') binary into the rootfs, and either
         call it @('init') or use some other name but symlink @('init') to it.
         Note: if you symlink to it, make sure the path your symlink points to
         is absolute, with @('/') referring to your rootfs, not your computer's
         @('/'). This may result in a symlink that is broken on your computer,
         but when Linux is running in the model, the rootfs will be mounted at
         @('/') so it'll work correctly.</p>

         <p>The last step is to create the cpio archive. Use the following command:</p>
         <code>
         find &lt;alpine rootfs path&gt; | cpio --quiet -H newc -o | gzip -9 -n &lt;archive path&gt;.img
         </code>

         <p>Make sure you aren't saving your cpio archive in the alpine rootfs.</p>

         <h3>Running Linux</h3>

         <p>Once you've built the kernel and the rootfs, you're ready to run
         Linux.</p>

         <p>While it isn't required, we recommend using the @(tsee
         bigmem-asymmetric::bigmem-asymmetric) memory model because it gives
         better performance. See @(tsee physical-memory-model) for more
         information about the memory models and how to switch.</p>

         <p>Run the following in an ACL2 session (assuming you're in the
         @('books/projects/x86isa') directory in the ACL2 source tree):</p>
         <code>
         (include-book \"tools/execution/top\")
         ;; This writes out some identity mapped page tables
         (init-sys-view #x10000000 x86)
         ;; Enable peripherals and exception handling
         (!enable-peripherals t x86)
         (!handle-exceptions t x86)
         ;; This function serves as our bootloader
         (linux-load \"&lt;path to kernel bzImage&gt;\"
                     \"&lt;path to rootfs archive&gt;\"
                     ;; The following is the kernel command line. Unless you
                     ;; know what you're doing, you don't have much reason to
                     ;; touch this
                     \"rootfstype=ramfs console=ttyprintk ignore_loglevel root=/dev/ram0\" x86
                     state)
         </code>

         <p>This will load Linux into the model. Optionally, if you wish to be
         able to interact with a shell on the machine over a TCP socket, you can
         run:</p>
         <code>
         (defttag :tty-raw)
         (include-raw \"machine/tty-raw.lsp\")
         </code>
         <p>After submitting the second form, the ACL2 session will hang. At
         this point you can connect to localhost on TCP port 6444 using a
         program like netcat or socat. For example, you can do this with netcat
         by executing the following in a shell:</p>
         <code>
         nc localhost 6444
         </code>
         <p>Once you connect, ACL2 should continue. Note: this utility only
         works in CCL and is unsound. Don't include it in proofs.</p>

         <p>Now, all you have to do is start execution. Submit the following form to ACL2:</p>
         <code>
         (x86-run-steps &lt;n&gt; x86)
         </code>
         <p>This will tell ACL2 to execute @('<n>') instructions. Booting Linux
         takes on the order of 600 million instructions. I usually just put in
         some large number (though you probably want to keep it a fixnum).</p>

         <p>As Linux boots, you should see the kernel log being printed in ACL2.
         Eventually, once Linux is done starting, it'll start @('/init'). The
         stdout of @('/init') will be printed to the kernel log. If you're using
         @('tty-raw.lsp'), you'll be able to interact with it over the
         socket.</p>

         <h3>The @('blkx86isa') device</h3>
         <p>The modified Linux kernel has support for a block device called
         @('blkx86isa'). This device is essentially a view into the gigabyte of
         physical memory at address @('0x100000000'). This could be useful for
         transfering files into and out of the Linux system running in the
         model.</p>

         <p>You can't mount it like any other drive on a Linux system, but you
         may notice that, if your system is configured as we did above,
         @('/dev') doesn't have a @('/dev/blkx86isa'). In fact, it doesn't have
         anything but the @('/dev/console') we constructed when building the
         rootfs. One can mount @('devtmpfs') on @('/dev') with the following
         command:</p>
         <code>
         mount -t devtmpfs none /dev
         </code>

         <p>After doing this, you'll find a @('/dev/blkx86isa') device (and
         other device files) in @('/dev'). You can use this like any other
         block device.</p>")

(defxdoc peripherals
         :parents (x86isa)
         :short "The various peripherals the @('x86isa') model contains"
         :long "<p>The @('x86isa') model supports a couple of peripherals.
         They only work when the @('enable-peripherals') field of the @('x86')
         stobj is @('t'). These include a timer and TTY. See their respective
         documentation topics below.</p>

         <p>The primary limitation when writing peripherals for the model is
         that the state can't change when memory is read. This is signficant
         because many real life peripherals change state when values are read
         from their memory mapped interface.</p>")

(defxdoc timer
         :parents (peripherals)
         :short "The timer device"
         :long "<p>The timer device can be used to receive an interrupt every
         100,000 instruction executions. If the interrupt flag is zero 100,000
         instructions after the last timer interrupt, we wait to send the
         interrupt until after they get reenabled. To enable this, make sure
         @('enable-peripherals') on the @('x86') stobj is @('t') and write a
         non-zero byte to physical memory address @('0x108'). Additionally, if
         to be able to handle the interrupt in software running on the model,
         make sure the @('handle-exceptions') field of the @('x86') stobj is
         also @('t').</p>

         <p>The timer device also writes the number of instructions that have
         been executed as a 64-bit unsigned integer to @('0x100'). This is the
         same value returned by the @(tsee x86-rdtsc) instruction.</p>")

;; ----------------------------------------------------------------------

(xdoc::order-subtopics
 X86ISA
 (introduction
  implemented-opcodes
  x86isa-build-instructions
  utils
  machine
  program-execution
  model-validation
  proof-utilities
  debugging-code-proofs
  contributors
  publications
  to-do))

(xdoc::order-subtopics
 implemented-opcodes
 (one-byte-opcodes-map
  two-byte-opcodes-map
  0f-38-three-byte-opcodes-map
  0f-3a-three-byte-opcodes-map))

(xdoc::order-subtopics
 instructions
 (implemented-opcodes
  opcode-maps
  instruction-semantic-functions
  one-byte-opcodes
  two-byte-opcodes
  fp-opcodes
  privileged-opcodes
  x86-illegal-instruction
  x86-step-unimplemented))

(xdoc::order-subtopics
 machine
 (x86isa-state
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
