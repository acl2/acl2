; x86isa assembly snippet testing framework
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

(in-package "X86ISA")

(include-book "../../../machine/x86")
(include-book "std/io/file-measure" :dir :system)
(local (include-book "std/io/open-channels" :dir :system))
(local (include-book "std/io/base" :dir :system))


(defxdoc asmtest
  :short "A simple framework for testing execution of small programs against
  the @(see x86isa) model."
  :long "

<p>The asmtest framework is designed to allow us to test many small
  programs (\"snippets\"), each many times on different data, and compare the
  results obtained by the x86 model with those obtained by running the programs
  on hardware.</p>

<p>A snippet is a C function or a piece of assembly code which reads a
fixed-size (per snippet) memory block of input and writes a fixed-size memory block of
output. A pointer to the input memory block is given in RDI/the first function
argument, and a pointer to the output memory block is given in RSI/the second
function argument.</p>

<p>To run a snippet on hardware, we use an executable into which all snippets
have been built.  This executable chooses a snippet to run, input file to read,
and output file to write based on its command line arguments.  The input file
is read into memory and interpreted as N input memory blocks; the execution
then runs the snippet N times on each successive input memory block, writing
out N output memory blocks to the output file.</p>

<p>To run a snippet on the x86 model, we read that executable into the x86
state and can then use the function @('test-snippet') to repeatedly run the
snippet on the model on the various inputs, comparing them to the outputs from
the executable.</p>

<p>Snippets are listed (along with their input and output block sizes) in
snippets.txt (under the asmtest directory,
books/projects/x86isa/tools/execution/asmtest).  This file is parsed by a
script that then generates the file snippets.h, used for building the asmtest
executable. Once the executable is built, the same script can be used to build
the file snippets.lsp, which tells ACL2 the input/output sizes and entry point
addresses of each snippet.</p>

<p>To add and test a new snippet:</p>
<ul>
<li>Add an entry to snippets.txt giving the name and input/output sizes.</li>

<li>Add an assembly function (with the same name as given in snippets.txt) to a
.nasm file in the snippets/ subdirectory (or add a new .nasm file). See
existing examples. (C functions could be supported too with small adjustments
to the makefile.)</li>

<li>Run @('make') in the asmtest directory to rebuild the asmtest executable
and remake snippets.lsp. (Note this should be done on an x86 machine with the
gcc, nasm, readelf, and python3. Perhaps we could use cross-compilation to do
this on other kinds of machines.)</li>

<li>Somehow generate a binary input file for your snippet. Its size should be
an integer multiple of the input block size of the snippet. One way to generate
basic random inputs is e.g. @('head -c nbytes /dev/urandom >
my_inputs.bin').</li>

<li>Execute your snippet on the input file, e.g. @('./asmtest -i my_inputs.bin
-o my_outputs.bin my_snippet')</li>

<li>Ensure that @('asmtest.lisp') is certified (this doesn't depend on previous
steps).</li>

<li>Test the outputs from the execution on the x86 model following the example
in @('example.lsp').</li>

</ul>
")

;; Fixtype for canonical-address
(define canonical-address-fix ((x canonical-address-p))
  :returns (new-x canonical-address-p)
  (mbe :logic (logext 48 x)
       :exec x)
  ///
  (defret <fn>-identity
    (implies (canonical-address-p x)
             (equal new-x x)))

  (fty::deffixtype canonical-address :pred canonical-address-p
    :fix canonical-address-fix
    :equiv canonical-address-equiv :define t :forward t))


;; Push fake address onto the stack
(define push-fake-return-address ((addr canonical-address-p)
                                  x86)
  :guard-hints (("goal" :in-theory (enable select-address-size)))
  (b* ((fake-return-address addr)
       (proc-mode *64-bit-mode*)
       (rsp (read-*sp proc-mode x86))
       (addr-size (select-address-size proc-mode nil x86))
       ((mv flg new-rsp) (add-to-*sp proc-mode rsp (- addr-size) x86))
       ((when flg) (er hard? 'x86-setup "Error in add-to-*sp: ~x0~%" flg) x86)
       ((mv flg x86)
        (wime-size *64-bit-mode* addr-size new-rsp *ss* fake-return-address
                   (alignment-checking-enabled-p x86) x86))
       ((when flg) (er hard? 'x86-setup "Error in wime-size: ~x0~%" flg) x86)
       (x86 (write-*sp proc-mode new-rsp x86)))
    x86))



(fty::defprod run-snippet-info
  ((input-size natp :rule-classes :type-prescription)
   (output-size posp :rule-classes :type-prescription)
   (snip-addr canonical-address-p)
   (ret-addr canonical-address-p)
   (step-count natp :rule-classes :type-prescription))
  ///
  (defthm integerp-of-run-snippet-info->snip-addr
    (integerp (run-snippet-info->snip-addr x))
    :hints (("goal" :use canonical-address-p-of-run-snippet-info->snip-addr
             :in-theory (disable canonical-address-p-of-run-snippet-info->snip-addr)))
    :rule-classes :type-prescription)

  (defthm integerp-of-run-snippet-info->ret-addr
    (integerp (run-snippet-info->ret-addr x))
    :hints (("goal" :use canonical-address-p-of-run-snippet-info->ret-addr
             :in-theory (disable canonical-address-p-of-run-snippet-info->ret-addr)))
    :rule-classes :type-prescription))

(local (defthm signed-byte-p-when-canonical-address-p
         (implies (canonical-address-p x)
                  (signed-byte-p 48 x))
         :hints(("Goal" :in-theory (enable canonical-address-p)))))

(define run-snippet ((input-addr :type (signed-byte 64))
                     (output-addr :type (signed-byte 64))
                     (snip-info run-snippet-info-p)
                     x86)
  :guard (b* (((run-snippet-info snip-info)))
           (unsigned-byte-p 59 snip-info.step-count))
  :guard-hints (("goal" :in-theory (disable canonical-address-p signed-byte-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable canonical-address-p))))
  (b* ((proc-mode *64-bit-mode*)
       ((run-snippet-info snip-info))
       (x86 (!rgfi *rdi* input-addr x86))
       (x86 (!rgfi *rsi* output-addr x86))
       (x86 (write-*ip proc-mode snip-info.snip-addr x86))
       (x86 (push-fake-return-address snip-info.ret-addr x86))
       (x86 (!ms nil x86))
       (x86 (!fault nil x86))
       (x86 (x86-run-halt snip-info.ret-addr snip-info.step-count x86))
       (fault (fault x86))
       (ms (ms x86))
       (rip (rip x86))
       (- (and (or fault
                   (not (case-match ms
                          ((('X86-FETCH-DECODE-EXECUTE-HALT ':RIP !snip-info.ret-addr))
                           t)
                          (& nil)))
                   (not (eql rip snip-info.ret-addr)))
               (raise "error: ~x0" (list fault ms rip)))))
    x86))

(define repeat-run-snippet ((n natp)
                            (input-addr :type (signed-byte 64))
                            (output-addr :type (signed-byte 64))
                            (snip-info run-snippet-info-p)
                            x86)
  :guard (b* (((run-snippet-info snip-info)))
           (and (canonical-address-p snip-info.snip-addr)
                (canonical-address-p snip-info.ret-addr)
                (unsigned-byte-p 59 snip-info.step-count)))
  (b* (((when (zp n)) x86)
       (x86 (run-snippet input-addr output-addr snip-info x86))
       ((run-snippet-info snip-info))
       (next-input-addr (+ snip-info.input-size input-addr))
       (next-output-addr (+ snip-info.output-size output-addr))
       ((unless (and (signed-byte-p 64 next-input-addr)
                     (signed-byte-p 64 next-output-addr)))
        (raise "address out of bounds")
        x86))
    (repeat-run-snippet (1- n) next-input-addr
                             next-output-addr
                             snip-info
                             x86)))

(local (in-theory (disable acl2::file-measure
                           read-byte$
                           open-input-channel-p1
                           state-p1
                           unsigned-byte-p)))


(defthm file-measure-of-read-byte$-other-channel
  (<= (acl2::file-measure chan (mv-nth 1 (read-byte$ channel state)))
      (acl2::file-measure chan state))
  :hints(("Goal" :in-theory (e/d (acl2::file-measure read-byte$))))
  :rule-classes :linear)

(define read-n-file-bytes ((n natp)
                           (channel symbolp)
                           state)
  :returns (mv eofp
               (bytes byte-listp) 
               (new-state
                (implies (open-input-channel-p1 channel :byte state)
                         (open-input-channel-p1 channel :byte state))))
  :guard (open-input-channel-p channel :byte state)
  (b* (((when (zp n)) (mv nil nil state))
       ((mv byte state) (read-byte$ channel state))
       ((unless byte) (mv t nil state))
       ((mv eofp rest state) (read-n-file-bytes (1- n) channel state)))
    (mv eofp
        (cons (mbe :logic (loghead 8 byte)
                   :exec byte)
              rest)
        state))
  ///
  (defret len-of-<fn>-when-not-eofp
    (implies (not eofp)
             (equal (len bytes) (nfix n))))

  (defret len-of-<fn>-when-eofp
    (implies eofp
             (< (len bytes) (nfix n)))
    :rule-classes :linear)

  (defret open-input-channel-p1-of-<fn>
    (implies (open-input-channel-p1 chan :byte state)
             (open-input-channel-p1 chan :byte new-state)))

  (defret file-measure-of-<fn>-weak
    (<= (acl2::file-measure chan new-state)
        (acl2::file-measure chan state))
    :rule-classes :linear)
  
  (defret file-measure-of-<fn>-strong
    (implies (and (not eofp)
                  (not (zp n)))
             (< (acl2::file-measure channel new-state)
                (acl2::file-measure channel state)))
    :rule-classes :linear))


(define n08-fix ((x n08p))
  :returns (new-x n08p)
  (mbe :logic (loghead 8 x) :exec x)
  ///
  (defret <fn>-identity
    (implies (n08p x) (equal new-x x)))

  (fty::deffixtype n08 :pred n08p :fix n08-fix :equiv n08-equiv :define t
  :forward t))

(fty::deflist byte-list :pred my-byte-listp
  :true-listp t :elt-type n08
  ///
  (defthm byte-listp-when-my-byte-listp
    (implies (my-byte-listp x)
             (byte-listp x)))

  (defthm my-byte-listp-when-byte-listp
    (implies (byte-listp x)
             (my-byte-listp x))))

(defprod snippet-mismatch
  ((input-bytes my-byte-listp)
   (expected-bytes my-byte-listp)
   (actual-bytes my-byte-listp)))

(fty::defoption maybe-snippet-mismatch snippet-mismatch-p)

(fty::deflist snippet-mismatch-list :elt-type snippet-mismatch :true-listp t)

(local (in-theory (disable (force))))

(define my-read-bytes-from-memory ((ptr canonical-address-p)
                                   (nbytes natp)
                                   x86)
  :guard (canonical-address-p (+ ptr nbytes))
  :returns (mv err (bytes byte-listp) x86)
  (b* (((mv err bytes x86) (read-bytes-from-memory ptr nbytes x86 nil)))
    (mv err (byte-list-fix bytes) x86)))

(define run-compare-snippet ((input-bytes byte-listp)
                             (output-bytes byte-listp)
                             (input-addr canonical-address-p)
                             (output-addr canonical-address-p)
                             (snip-info run-snippet-info-p)
                             x86)
  :returns (mv (mismatch maybe-snippet-mismatch-p)
               new-x86)
  :guard-hints (("goal" :in-theory (disable canonical-address-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable canonical-address-p))))
  :guard (b* (((run-snippet-info snip-info)))
           (and (canonical-address-p snip-info.snip-addr)
                (canonical-address-p snip-info.ret-addr)
                (unsigned-byte-p 59 snip-info.step-count)
                (canonical-address-p (+ input-addr (len input-bytes)))
                (canonical-address-p (+ output-addr snip-info.output-size))))
  (b* (((run-snippet-info snip-info))
       ((mv err x86) (write-bytes-to-memory input-addr input-bytes x86))
       ((when err)
        (raise "error writing input bytes to memory: ~x0" err)
        (mv nil x86))
       (x86 (run-snippet input-addr output-addr snip-info x86))
       ((mv err result-bytes x86)
        (my-read-bytes-from-memory output-addr snip-info.output-size x86))
       ((when err)
        (raise "error reading output bytes from memory: ~x0" err)
        (mv nil x86))
       ((when (equal result-bytes output-bytes)) (mv nil x86)))
    (cw-print-base-radix 16 "Mismatch: input ~x0~%expected ~x1~%actual   ~x2~%"
                         input-bytes output-bytes result-bytes)
    (mv (make-snippet-mismatch :input-bytes input-bytes
                               :expected-bytes output-bytes
                               :actual-bytes result-bytes)
        x86)))



(defprod run-snippet-file-info
  ((snip-info run-snippet-info)
   (input-addr canonical-address-p)
   (output-addr canonical-address-p)
   (input-channel symbolp)
   (output-channel symbolp)))

(define run-compare-snippet-from-files ((info run-snippet-file-info-p)
                                        x86 state)
  :guard (b* (((run-snippet-file-info info))
              ((run-snippet-info snip-info) info.snip-info))
           (and (canonical-address-p snip-info.snip-addr)
                (canonical-address-p snip-info.ret-addr)
                (unsigned-byte-p 59 snip-info.step-count)
                (canonical-address-p (+ info.input-addr snip-info.input-size))
                (canonical-address-p (+ info.output-addr snip-info.output-size))
                (open-input-channel-p info.input-channel :byte state)
                (open-input-channel-p info.output-channel :byte state)))
  :returns (mv (mismatch maybe-snippet-mismatch-p)
               eofp
               new-x86 new-state)
  :guard-hints (("goal" :in-theory (disable canonical-address-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable canonical-address-p))))
  (b* (((run-snippet-file-info info))
       ((run-snippet-info snip-info) info.snip-info)
       ((mv in-eofp input-bytes state)
        (read-n-file-bytes snip-info.input-size info.input-channel state))
       ((mv out-eofp output-bytes state)
        (read-n-file-bytes snip-info.output-size info.output-channel state))
       ((when (or in-eofp out-eofp))
        ;; Check some unexpected conditions
        (and in-eofp input-bytes
             (raise "Input file size wasn't divisible by input size -- extra ~
                     ~x0 bytes" (len input-bytes)))
        (and out-eofp output-bytes
             (raise "Output file size wasn't divisible by output size -- ~
                     extra ~x0 bytes" (len output-bytes)))
        (and in-eofp (not out-eofp)
             (raise "More output than input entries"))
        (and out-eofp (not in-eofp)
             (raise "More input than outut entries"))
        (mv nil t x86 state))
       ((mv mismatch x86)
        (run-compare-snippet input-bytes output-bytes
                             info.input-addr info.output-addr
                             snip-info x86)))
    (mv mismatch nil x86 state))
  ///
  (defret file-measure-of-<fn>-weak
    (<= (acl2::file-measure (run-snippet-file-info->output-channel info) new-state)
        (acl2::file-measure (run-snippet-file-info->output-channel info)
                            state))
    :rule-classes :linear)

  (defret file-measure-of-<fn>-string
    (implies (not eofp)
             (< (acl2::file-measure (run-snippet-file-info->output-channel info) new-state)
                (acl2::file-measure (run-snippet-file-info->output-channel info)
                                    state)))
    :rule-classes :linear)

  (defret open-input-channel-p1-of-<fn>
    (implies (open-input-channel-p1 chan :byte state)
             (open-input-channel-p1 chan :byte new-state))))


(define repeat-run-compare-snippet-from-files ((info run-snippet-file-info-p)
                                               x86 state
                                               &key (stop-on-mismatch 'nil))
  :guard (b* (((run-snippet-file-info info))
              ((run-snippet-info snip-info) info.snip-info))
           (and (canonical-address-p snip-info.snip-addr)
                (canonical-address-p snip-info.ret-addr)
                (unsigned-byte-p 59 snip-info.step-count)
                (canonical-address-p (+ info.input-addr snip-info.input-size))
                (canonical-address-p (+ info.output-addr snip-info.output-size))
                (open-input-channel-p info.input-channel :byte state)
                (open-input-channel-p info.output-channel :byte state)))
  :measure (acl2::file-measure (run-snippet-file-info->output-channel info) state)
  :returns (mv (mismatches snippet-mismatch-list-p)
               new-x86 new-state)
  :guard-hints (("goal" :in-theory (disable canonical-address-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable canonical-address-p))))
  (b* (((mv mismatch eofp x86 state)
        (run-compare-snippet-from-files info x86 state))
       ((when eofp) (mv nil x86 state))
       ((when stop-on-mismatch)
        (if mismatch
            (mv (list mismatch) x86 state)
          (repeat-run-compare-snippet-from-files info x86 state :stop-on-mismatch t)))
       ((mv rest x86 state)
        (repeat-run-compare-snippet-from-files info x86 state :stop-on-mismatch nil)))
    (mv (if mismatch
            (cons mismatch rest)
          rest)
        x86 state))
  ///
  (defret open-input-channel-p1-of-<fn>
    (implies (open-input-channel-p1 chan :byte state)
             (open-input-channel-p1 chan :byte new-state))))

(define close-byte-input-channel ((channel symbolp) state)
  :guard (open-input-channel-p channel :byte state)
  :enabled t
  (if (or (eq channel 'acl2-input-channel::standard-character-input-0)
          (eq channel 'acl2-input-channel::standard-object-input-0))
      state
    (close-input-channel channel state)))


(define test-snippet-aux (&key (input-file stringp)
                               (output-file stringp)
                               (input-size natp)
                               (output-size posp)
                               (snippet-addr canonical-address-p)
                               ((input-addr canonical-address-p) '#x10000000000)
                               ((output-addr canonical-address-p) '#x18000000000)
                               ((ret-addr canonical-address-p) '#x-DEADEADBEEF)
                               (stop-on-mismatch 'nil)
                               ((step-count natp) '10000)
                               (x86 'x86)
                               (state 'state))
  :returns (mv (mismatches snippet-mismatch-list-p)
               new-x86 new-state)
  (b* (((mv input-channel state) (open-input-channel input-file :byte state))
       ((unless input-channel)
        (raise "Couldn't open input file ~x0" input-file)
        (mv nil x86 state))
       ((mv output-channel state) (open-input-channel output-file :byte state))
       ((unless output-channel)
        (raise "Couldn't open output file ~x0" output-file)
        (mv nil x86 state))
       ((when (eq input-channel output-channel))
        (raise "Input and output channels were the same? probably impossible")
        (mv nil x86 state))
       ((unless (canonical-address-p (+ output-addr output-size)))
        (raise "Bad output addr+size") (mv nil x86 state))
       ((unless (canonical-address-p (+ input-addr input-size)))
        (raise "Bad input addr+size") (mv nil x86 state))
       ((unless (unsigned-byte-p 59 step-count))
        (raise "Bad step-count") (mv nil x86 state))
       (info (make-run-snippet-file-info
              :snip-info (make-run-snippet-info :input-size input-size
                                                :output-size output-size
                                                :snip-addr snippet-addr
                                                :ret-addr ret-addr
                                                :step-count step-count)
              :input-addr input-addr
              :output-addr output-addr
              :input-channel input-channel
              :output-channel output-channel))
       ((mv mismatches x86 state)
        (repeat-run-compare-snippet-from-files info x86 state :stop-on-mismatch stop-on-mismatch))
       (state (close-byte-input-channel input-channel state))
       (state (close-byte-input-channel output-channel state)))
    (mv mismatches x86 state)))





;; Abstract snippet-data table -- load with DEF-SNIPPET-DATA

(defprod snippet-info
  ((name stringp :rule-classes :type-prescription)
   (input-size natp :rule-classes :type-prescription)
   (output-size posp :rule-classes :type-prescription)
   (addr canonical-address-p))
  :layout :list)

(fty::deflist snippet-table :elt-type snippet-info :true-listp t
  ///
  (defthm alistp-when-snippet-table-p-fwd
    (implies (snippet-table-p x)
             (alistp x))
    :rule-classes :forward-chaining))

(encapsulate
  (((snippet-data) => * :guard t :formals nil))

  (local (defun snippet-data ()
           (declare (xargs :guard t))
           nil))

  (defthm snippet-table-p-of-snippet-data
    (snippet-table-p (snippet-data))))

(defthm alistp-of-snippet-data
  (alistp (snippet-data)))

(defthm snippet-info-p-of-assoc-equal-when-snippet-table-p
  (implies (and (snippet-table-p x)
                (assoc-equal name x))
           (snippet-info-p (assoc-equal name x))))


(defmacro def-snippet-data (name)
  (let ((namestar (intern-in-package-of-symbol
                   (concatenate 'string "*" (symbol-name name) "*")
                   name)))
    `(progn
       (defconsts (& ,namestar state)
         (acl2::read-file "snippets.lsp" state))

       (define ,name ()
         ,namestar
         ///
         (defattach snippet-data ,name)))))





(define test-snippet ((name stringp)
                      &key (input-file stringp)
                      (output-file stringp)
                      ((input-addr canonical-address-p) '#x10000000000)
                      ((output-addr canonical-address-p) '#x18000000000)
                      ((ret-addr canonical-address-p) '#x-DEADEADBEEF)
                      (stop-on-mismatch 'nil)
                      ((step-count natp) '10000)
                      (x86 'x86)
                      (state 'state))
  :returns (mv (mismatches snippet-mismatch-list-p)
               new-x86 new-state)
  (b* ((snip (assoc-equal name (snippet-data)))
       ((unless snip)
        (raise "Not found: ~s0" name)
        (mv nil x86 state))
       ((snippet-info snip)))
    (test-snippet-aux :input-file input-file
                      :output-file output-file
                      :input-size snip.input-size
                      :output-size snip.output-size
                      :snippet-addr snip.addr
                      :input-addr input-addr
                      :output-addr output-addr
                      :ret-addr ret-addr
                      :stop-on-mismatch stop-on-mismatch
                      :step-count step-count
                      :x86 x86)))
