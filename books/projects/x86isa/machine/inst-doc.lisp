; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Shilpi Goel
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
; Shilpi Goel         <shigoel@gmail.com>

(in-package "X86ISA")

(include-book "inst-listing")



;; ----------------------------------------------------------------------

;; Creating documentation for the implemented opcodes:

(defconst *x86isa-printconfig*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 16
   :print-radix t
   :print-lowercase t))

(defconst *x86isa-printconfig-uppercase*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 16
   :print-radix t
   :print-lowercase nil))

(defconst *x86isa-printconfig-base-10*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 10
   :print-radix nil
   :print-lowercase nil))

(defconst *x86isa-printconfig-base-10-lowercase*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 10
   :print-radix nil
   :print-lowercase t))


(include-book "std/strings/printtree-fty" :dir :system)


(define opcode-print-syms ((acc str::printtree-p)
                           (syms symbol-listp))
  :returns (new-acc str::printtree-p)
  (cond ((atom syms)
         (str::printtree-fix acc))
        ((atom (cdr syms))
         (str::pcat acc (symbol-name (car syms))))
        (t (opcode-print-syms (str::pcat acc (symbol-name (car syms)) ".") (cdr syms)))))
      

;; examples: EVEX.512.66.0F.W0 6F /r
;;           VEX.128.66.0F.WIG 7F /r
;;           F3 0F 10 /r



(define opcode-string-bytes ((acc str::printtree-p)
                             (x natp))
  :returns (new-acc str::printtree-p)
  :verify-guards nil
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (defthm logcdr-less-when-not-zp
                      (and (implies (natp x)
                                    (<= (logcdr x) x))
                           (implies (posp x)
                                    (< (logcdr x) x)))
                      :hints (("goal" :use ((:instance acl2::logcar-logcdr-elim
                                             (i x)))
                               :in-theory (e/d (logcons)
                                               (bitops::logcons-destruct))))
                      :rule-classes :linear))

             (local (defthm logtail-less-when-not-zp
                      (and (implies (and (not (zp x))
                                         (not (Zp n)))
                                    (< (logtail n x) x))
                           (implies (natp x)
                                    (<= (logtail n x) x)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions bitops::ihsext-recursive-redefs))))))
  (b* (((when (zp x)) (str::printtree-fix acc))
       (acc (opcode-string-bytes acc (logtail 8 x)))
       (acc (if (eql 0 (logtail 8 x)) acc (str::pcat acc " ")))
       (digits (str::nat-to-hex-string (loghead 8 x)))
       (digits (cond ((eql (length digits) 0) "00")
                     ((eql (length digits) 1) (str::pcat "0" digits))
                     (t digits))))
    (str::pcat acc digits))
  ///
  (verify-guards opcode-string-bytes))

(define opcode-prefix-string ((acc str::printtree-p)
                              (pfx op-pfx-p))
  :returns (new-acc str::printtree-p)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable op-pfx-p))))
  (cond (pfx (b* ((pfx (case pfx
                         (:no-prefix :np)
                         (t pfx))))
               (str::pcat acc (symbol-name pfx) " ")))
        (t (str::printtree-fix acc))))

(defconst *evex-syms-for-opcode-string*
  (set-difference-equal *evex-pfx-cases* *vvvv-pfx*))

(defconst *vex-syms-for-opcode-string*
  (set-difference-equal *vex-pfx-cases* *vvvv-pfx*))

(define opcode-string ((x opcode-p))
  ;; NOT complete!
  :prepwork ((local (defthm symbol-listp-of-intersection-equal
                      (implies (symbol-listp x)
                               (symbol-listp (intersection-equal x y)))))
             (local (in-theory (disable loghead)))
             (local (in-theory (disable intersection-equal))))
  (b* (((opcode x))
       (acc nil)
       (acc (opcode-prefix-string acc x.pfx))
       (acc (cond (x.evex
                   (b* ((acc (opcode-print-syms acc (cons 'evex (intersection-eq *evex-syms-for-opcode-string* x.evex)))))
                     (str::pcat acc " ")))
                  (x.vex
                   (B* ((acc (opcode-print-syms acc (cons 'vex (intersection-eq *vex-syms-for-opcode-string* x.vex)))))
                     (str::pcat acc " ")))
                  (t acc)))
       (opcode-bytes (if (or x.evex x.vex)
                         (loghead 8 x.op)
                       x.op))
       (acc (opcode-string-bytes acc opcode-bytes)))
    (str::printtree->str acc)))


(define create-inst-doc ((inst inst-p)
                         &key
                         ((fn-ok? booleanp
                                  "Include information about the semantic
                          function in the documentation or not")
                          't)
                         ((arg-ok? booleanp
                                   "Include information about the
                          operands (@('inst.operands') field) in the
                          documentation or not")
                          'nil)
                         ((full-opcode? booleanp
                                        "Include a SDM-like representation of
                         the full opcode, not just the low byte")
                          'nil))

  :guard-hints (("Goal" :in-theory (e/d () (subseq))))
  :returns (inst-doc-string stringp)

  :prepwork

  ((define symbol-list-to-string ((lst symbol-listp))
     :returns (newstr stringp :hyp :guard)
     (if (atom lst)
         ""
       (if (eql (len lst) 1)
           (str::cat ":" (symbol-name (car lst)))
         (str::cat ":" (symbol-name (car lst)) " "
                   (symbol-list-to-string (cdr lst))))))

   (define create-extra-info-doc-string (info
                                         (text stringp))
     :returns (doc stringp :hyp :guard)

     (if info
         (let* ((info-string (cond ((symbolp info)
                                    (str::cat ":" (symbol-name info)))
                                   ((symbol-listp info)
                                    (symbol-list-to-string info))
                                   (t
                                    (str::pretty
                                     info
                                     :config
                                     *x86isa-printconfig-base-10*)))))
           (str::cat "<tr><td> @('" text "') </td>"
                     "<td> @('" info-string "') </td> </tr>"))
       ""))

   (define create-extra-info-doc ((opcode strict-opcode-p))
     :returns (doc stringp :hyp :guard)

     (b* (((opcode opcode))
          (feat-doc  (create-extra-info-doc-string opcode.feat ":FEAT "))
          (vex-doc   (create-extra-info-doc-string opcode.vex  ":VEX "))
          (evex-doc  (create-extra-info-doc-string opcode.evex ":EVEX "))
          (pfx-doc   (create-extra-info-doc-string opcode.pfx  ":PFX "))
          (mode-doc  (create-extra-info-doc-string opcode.mode ":MODE "))
          (reg-doc   (create-extra-info-doc-string opcode.reg  ":REG "))
          (mod-doc   (create-extra-info-doc-string opcode.mod  ":MOD "))
          (r/m-doc   (create-extra-info-doc-string opcode.r/m  ":R/M "))
          (rex-doc   (create-extra-info-doc-string opcode.rex  ":REX "))
          (extra-info (str::cat "<table>"
                                mode-doc pfx-doc reg-doc
                                mod-doc r/m-doc rex-doc
                                vex-doc evex-doc feat-doc
                                "</table>")))
       extra-info))

   (define gen-addressing-method-code-doc ((z-info alistp))
     ;; (gen-addressing-method-code-doc *Z-addressing-method-info*)
     :prepwork
     ((define get-addressing-method-doc ((code addressing-method-code-p))
        :returns (str stringp)
        (b* ((alst (cdr (assoc-equal code *Z-addressing-method-info*)))
             (doc (cdr (assoc-equal :doc alst)))
             ((unless doc) ""))
          doc)))
     (if (endp z-info)
         nil
       (b* ((code (caar z-info))
            ((unless (addressing-method-code-p code))
             (er hard? __function__ "~% Bad code ~x0 encountered! ~%" code))
            (codestr (str::pretty code :config *x86isa-printconfig-base-10*))
            (docstr (str::cat "@(' " codestr "'): " (get-addressing-method-doc code)))
            (topic-name (intern$ (str::cat codestr "-Z-ADDRESSING-METHOD") "X86ISA"))
            (form `((defxdoc ,topic-name
                      ;; We intentionally don't define a parent here.  We can
                      ;; wrap the call of this function inside an appropriate
                      ;; defsection if we want to generate addressing method
                      ;; information.
                      :long ,docstr)))
            (rest (gen-addressing-method-code-doc (cdr z-info))))
         (append form rest))))

   (define gen-operand-type-code-doc ((info alistp))
     ;; (gen-operand-type-code-doc *operand-type-code-info*)
     :prepwork
     ((define get-operand-type-code-doc ((code operand-type-code-p))
        :returns (str stringp)
        (b* ((alst (cdr (assoc-equal code *operand-type-code-info*)))
             (doc (cdr (assoc-equal :doc alst)))
             ((unless doc) ""))
          doc)))
     (if (endp info)
         nil
       (b* ((code (caar info))
            ((unless (operand-type-code-p code))
             (er hard? __function__ "~% Bad code ~x0 encountered! ~%" code))
            (codestr (str::pretty code :config *x86isa-printconfig-base-10-lowercase*))
            (docstr (str::cat "@(' " codestr "'): " (get-operand-type-code-doc code)))
            (topic-name (intern$
                         (str::upcase-string (str::cat codestr "-OPERAND-TYPE-CODE"))
                         "X86ISA"))
            (form `((defxdoc ,topic-name
                      ;; We intentionally don't define a parent here.  We can
                      ;; wrap the call of this function inside an appropriate
                      ;; defsection if we want to generate operand code type
                      ;; information.
                      :long ,docstr)))
            (rest (gen-operand-type-code-doc (cdr info))))
         (append form rest))))

   (define create-arg-doc ((x operand-type-p))
     :returns (xstr stringp)
     (cond
      ((atom x) " ")
      ((eql (len x) 1)
       (b* ((possible-code (nth 0 x))
            (codestr (str::pretty possible-code :config *x86isa-printconfig-base-10*))
            (topic-name (str::cat codestr "-Z-ADDRESSING-METHOD")))
         (if (addressing-method-code-p possible-code)
             (str::cat "[<a href=\"index.html?topic=X86ISA____" topic-name "\">" codestr "</a>] ")
           (str::cat "[@('" codestr "')] "))))
      ((eql (len x) 2)
       (b* ((addressing-mode (nth 0 x))
            (addressing-mode-str ;; Addressing Method Code in Upper Case
             (str::pretty addressing-mode :config *x86isa-printconfig-base-10*))
            (addressing-mode-topic-name
             (str::cat addressing-mode-str "-Z-ADDRESSING-METHOD"))
            (operand-code (nth 1 x))
            (operand-code-str ;; Operand Type Code in Lower Case
             (str::pretty operand-code :config *x86isa-printconfig-base-10-lowercase*))
            (operand-code-topic-name
             (str::upcase-string (str::cat operand-code-str "-OPERAND-TYPE-CODE"))))
         (str::cat
          "[<a href=\"index.html?topic=X86ISA____" addressing-mode-topic-name "\">"
          addressing-mode-str
          "</a> - <a href=\"index.html?topic=X86ISA____" operand-code-topic-name "\">"
          operand-code-str "</a>] ")))
      (t " ")))

   (define create-args-doc ((operands maybe-operands-p))
     :prepwork ((local (in-theory (e/d (maybe-operands-p) ()))))
     :returns (docstr stringp)
     (b* (((unless operands)
           ;; Instruction does not require any operands.
           "<td> </td>")
          ((operands operands))
          (op1 (create-arg-doc operands.op1))
          ((if (eql operands.op2 nil))
           (str::cat "<td> " op1 " </td>"))
          (op2 (create-arg-doc operands.op2))
          ((if (eql operands.op3 nil))
           (str::cat "<td> " op1 ", " op2 " </td>"))
          (op3 (create-arg-doc operands.op3))
          ((if (eql operands.op4 nil))
           (str::cat "<td> " op1 ", " op2 ", " op3 " </td>"))
          (op4 (create-arg-doc operands.op4)))
       (str::cat "<td> " op1 ", " op2 ", " op3 ", " op4 " </td>")))

   (defthm inst-p-implies-mnemonic-p
     (implies (inst-p x)
              (mnemonic-p (inst->mnemonic x)))
     :hints (("Goal" :in-theory (e/d (inst-p) ())))
     :rule-classes :forward-chaining)

   (defthm inst-p-implies-consp-fn
     (implies (and (inst-p x)
                   (inst->fn x))
              (consp (inst->fn x)))
     :hints (("Goal" :in-theory (e/d (fn-desc-p inst->fn fn-desc-p) ())))))

  (b* (((inst inst))
       (opcode inst.opcode)
       ((opcode opcode))
       ;; We only add the low 8 bits of the opcode in the documentation for
       ;; three reasons: (1) to save horizontal space in the table; (2) the
       ;; table headings will list whether we're dealing with one-, two-, or
       ;; three-byte map, and in the last two cases, will mention whether the
       ;; opcode bytes begin with 0F_38 or 0F_3A; and (3) VEX- and EVEX-encoded
       ;; opcodes don't really have two- or three-byte opcodes because the map
       ;; is encoded in the VEX/EVEX prefixes, so it can be misleading to list
       ;; their opcode as two or three bytes long.
       (opcode-str (if full-opcode?
                       (opcode-string opcode)
                       (subseq (str::hexify-width (loghead 8 opcode.op) 2) 3 nil)))
       (mnemonic (if (stringp inst.mnemonic)
                     inst.mnemonic
                   (symbol-name inst.mnemonic)))
       (fn-info  (if (and fn-ok? inst.fn)
                     (if (eql (car inst.fn) :NO-INSTRUCTION)
                         "@('NO INSTRUCTION')"
                       (concatenate
                        'string
                        "@(tsee "
                        (str::pretty (car inst.fn) :config *x86isa-printconfig*)
                        ") "
                        (if (cdr inst.fn)
                            (concatenate
                             'string
                             "-- <br/><tt>"
                             (str::pretty (cdr inst.fn)
                                          :config *x86isa-printconfig*)
                             "</tt>")
                          "")))
                   ""))
       (fn-info (if fn-ok?
                    (concatenate
                     'string
                     " <td> " fn-info                 " </td> ")
                  ""))
       ;; --------------------------------------------------
       ;; Constructing extra-info documentation:
       (extra-info (create-extra-info-doc opcode))
       ;; --------------------------------------------------
       ;; Constructing operands' documentation, if necessary:
       (arg-str (if arg-ok? (create-args-doc inst.operands) ""))
       ;; --------------------------------------------------
       (doc-string
        (concatenate
         'string
         "<tr> "
         " <td> " opcode-str " </td> "
         " <td> " mnemonic                " </td> "
         " <td> " extra-info              " </td> "
                  arg-str
                  fn-info
         "</tr>")))
    doc-string))

(define create-insts-doc-aux ((inst-lst inst-list-p)
                              &key
                              ((fn-ok? booleanp
                                       "Include information about the semantic
                          function in the documentation or not")
                               't)
                              ((arg-ok? booleanp
                                        "Include information about the
                          operands (@('inst.operands') field) in the
                          documentation or not")
                               'nil)
                         ((full-opcode? booleanp
                                        "Include a SDM-like representation of
                         the full opcode, not just the low byte")
                          'nil))

  :returns (insts-doc-string stringp)

  (if (endp inst-lst)
      ""
    (concatenate
     'string
     (create-inst-doc (car inst-lst) :fn-ok? fn-ok? :arg-ok? arg-ok? :full-opcode? full-opcode?)
     (create-insts-doc-aux (cdr inst-lst) :fn-ok? fn-ok? :arg-ok? arg-ok? :full-opcode? full-opcode?))))

(define create-insts-doc ((inst-lst inst-list-p)
                          &key
                          ((fn-ok? booleanp
                                   "Include information about the semantic
                          function in the documentation or not")
                           't)
                          ((arg-ok? booleanp
                                    "Include information about the
                          operands (@('inst.operands') field) in the
                          documentation or not")
                           'nil)
                         ((full-opcode? booleanp
                                        "Include a SDM-like representation of
                         the full opcode, not just the low byte")
                          'nil))

  :returns (insts-doc-string stringp)

  (b* ((insts-doc-string (create-insts-doc-aux
                          inst-lst :fn-ok? fn-ok? :arg-ok? arg-ok? :full-opcode? full-opcode?))
       (table-header-1 "<th> Opcode </th>")
       (table-header-2 "<th> Mnemonic </th>")
       (table-header-3 "<th> Other Information </th>")
       (table-header-4 (if arg-ok?
                           "<th> Operands </th>"
                         ""))
       (table-header-5 (if fn-ok?
                           "<th> Semantic Function </th>"
                         ""))
       (table-header (concatenate
                      'string "<tr> "
                      table-header-1 table-header-2
                      table-header-3 table-header-4
                      table-header-5
                      " </tr>")))
    (concatenate
     'string
     "<table> " table-header insts-doc-string " </table>")))


(make-event
 ;; To generate ALL the instructions, including the unimplemented ones, set
 ;; :fn? to nil in the following forms.
 (b* ((one (create-insts-doc
            (select-insts *one-byte-opcode-map*
                          :get/rem :get
                          :fn? t)))
      (two (create-insts-doc
            (select-insts *two-byte-opcode-map*
                          :get/rem :get
                          :fn? t)))
      (three-1 (create-insts-doc
                (select-insts *0F-38-three-byte-opcode-map*
                              :get/rem :get
                              :fn? t)))
      (three-2 (create-insts-doc
                (select-insts *0F-3A-three-byte-opcode-map*
                              :get/rem :get
                              :fn? t))))
   `(progn
      (defsection one-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is one byte long"
        :long ,one)
      (defsection two-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is two bytes long,
       beginning with @('0F'); includes VEX/EVEX instructions too"
        :long ,two)
      (defsection 0F-38-three-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is three bytes
       long, beginning with @('0F_38'); includes VEX/EVEX instructions too"
        :long ,three-1)
      (defsection 0F-3A-three-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is three bytes
       long, beginning with @('0F_3A'); includes VEX/EVEX instructions too"
        :long ,three-2))))


(defsection implemented-opcodes
  :parents (x86isa instructions x86-decoder opcode-maps)
  :short "Intel opcodes supported in @('x86isa')."
  :long
  "<p>We support decoding of all the x86 instructions in the one-, two-, and
 three-byte opcode maps, including the AVX/AVX2/AVX512 extensions.  However, a
 fraction of those are actually implemented in this model --- when we say
 <i>implemented</i> instructions, we mean instructions that have a semantic function
 that models its effects on the machine's state.</p>

 <p>For a listing of all such supported instructions, see @(see
 one-byte-opcodes-map), @(see two-byte-opcodes-map), @(see
 0f-38-three-byte-opcodes-map), and @(see 0f-3a-three-byte-opcodes-map).</p>

 <p>For a readable version of all the opcode maps, see constants like
  @('*pre-one-byte-opcode-map*') in the book @('inst-listing.lisp').  These are
  the constants to edit in order to add new instructions, etc. in the future.
  The dispatch, modr/m and prefixes computation, and generation of
  documentation is done automatically from these constants.</p>")

;; ----------------------------------------------------------------------
