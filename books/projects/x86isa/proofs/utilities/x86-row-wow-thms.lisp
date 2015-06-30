;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "basics"
	      :ttags (:include-raw :undef-flg :syscall-exec :other-non-det))

;; ===================================================================

(defsection x86-RoW-WoW-thms

  :parents (proof-utilities)

  :short "Theorems about interactions between the fields of @('x86')
  and other top-level state accessor and updater functions"

  :long "<p>A program's behavior can be described by the effects it has
to the state of the machine.  Given an initial state, the final state
may be described as a nest of updates made in program order to the
initial state.  In order to reason about the behavior of a program, we
need to develop lemmas to read from, write to, and re-arrange these
nests of updates.  This book contains the following kinds of
theorems:</p>

<ul>

<li><b>Read-over-Write Theorems:</b> <p>There are two types of
  Read-Over-Write theorems.  The first describes the independence or
  non-interference of different components of the x86 state.  One
  example is proving that an update made to a specific register does
  not modify the value of any other component of the x86 state.  The
  second asserts that reading a component after it is modified returns
  the value that was written to it during the modification.</p></li>

<li><b>Write-over-Write Theorems:</b> <p>Like the Read-Over-Write
  theorems, there are two types of Write-over-Write theorems.  The
  first asserts that independent writes to the x86 state can commute
  safely.  The second asserts that if consecutive writes are made to a
  component, the most recent write is the only visible write.</p></li>

<li><b>Preservation Theorems:</b> <p>These types of theorems assert
  that writing a valid value to a component in a valid x86 state
  returns a modified x86 state that is still valid.</p></li>

</ul>"
  )

(local (xdoc::set-default-parents x86-RoW-WoW-thms))

;; ======================================================================

(local
 (in-theory (e/d* (abstract-stobj-fns-ruleset memi !memi x86p)
		  ())))

;; ======================================================================

(defconst *pos-func-name*  0)
(defconst *pos-inputs*     1)
(defconst *pos-input-x86*  2)
(defconst *pos-outputs*    3)
(defconst *pos-output-x86* 4)
(defconst *pos-hypotheses* 5)
(defconst *pos-hints*      6)
(defconst *pos-dont-pair*  7)
(defconst *alt-name*       8)

;; Format of reader/writer functions list:
;; (
;;  :FUNCTION-NAME
;;  :INPUTS
;;  :INPUT-POSITION-OF-X86
;;  :OUTPUTS
;;  :OUTPUT-POSITION-OF-X86
;;  :HYPOTHESES
;;  :HINTS
;;  :DO-NOT-PAIR-LIST
;;  :PREFERRED-NAME (default if nil)
;;  )

;; ======================================================================

;; Readers:

(defconst *x86-state-primitive-readers*
  ;; Use I for the indices here.
  '(
    ;; I've put programmer-level-mode as the first reader so that we have
    ;; all the lemmas we need when we set about proving theorems like
    ;; rgfi-wb.

    (programmer-level-mode
     (x86)
     0
     ((-1 . booleanp))
     -1
     nil
     nil
     (programmer-level-mode !programmer-level-mode))

    (rgfi
     (i x86)
     1
     ((-1 . (signed-byte 64)))
     -1
     nil
     nil
     (rgfi !rgfi rr08 rr16
      rr32 rr64 !rgfi-size rgfi-size))

    (rip
     (x86)
     0
     ((-1 . (signed-byte 48)))
     -1
     nil
     nil
     (rip !rip))

    (rflags
     (x86)
     0
     ((-1 . (unsigned-byte 32)))
     -1
     nil
     nil
     (rflags !rflags flgi !flgi))


    (memi
     (i x86)
     1
     ((-1 . (unsigned-byte 52)))
     -1
     nil
     nil
     (memi !memi wvm08 wvm16 wvm32 wvm64 wm08 wm16 wm32 wm64 wb wm-size))

    (seg-visiblei
     (i x86)
     1
     ((-1 . (unsigned-byte 16)))
     -1
     nil
     nil
     (seg-visiblei !seg-visiblei))

    (seg-hiddeni
     (i x86)
     1
     ((-1 . (unsigned-byte 112)))
     -1
     nil
     nil
     (seg-hiddeni !seg-hiddeni))

    (stri
     (i x86)
     1
     ((-1 . (unsigned-byte 80)))
     -1
     nil
     nil
     (stri !stri))

    (ssr-visiblei
     (i x86)
     1
     ((-1 . (unsigned-byte 16)))
     -1
     nil
     nil
     (ssr-visiblei !ssr-visiblei))

    (ssr-hiddeni
     (i x86)
     1
     ((-1 . (unsigned-byte 112)))
     -1
     nil
     nil
     (ssr-hiddeni !ssr-hiddeni))

    (ctri
     (i x86)
     1
     ((-1 . (unsigned-byte 64)))
     -1
     nil
     nil
     (ctri !ctri))

    (dbgi
     (i x86)
     1
     ((-1 . (unsigned-byte 64)))
     -1
     nil
     nil
     (dbgi !dbgi))

    (fp-datai
     (i x86)
     1
     ((-1 . (unsigned-byte 80)))
     -1
     nil
     nil
     (fp-datai !fp-datai))

    (fp-ctrl
     (x86)
     1
     ((-1 . (unsigned-byte 16)))
     -1
     nil
     nil
     (fp-ctrl !fp-ctrl))

    (fp-status
     (x86)
     1
     ((-1 . (unsigned-byte 16)))
     -1
     nil
     nil
     (fp-status !fp-status))

    (fp-tag
     (x86)
     1
     ((-1 . (unsigned-byte 16)))
     -1
     nil
     nil
     (fp-tag !fp-tag))

    (fp-last-inst
     (x86)
     1
     ((-1 . (unsigned-byte 48)))
     -1
     nil
     nil
     (fp-last-inst !fp-last-inst))

    (fp-last-data
     (x86)
     1
     ((-1 . (unsigned-byte 48)))
     -1
     nil
     nil
     (fp-last-data !fp-last-data))

    (fp-opcode
     (x86)
     1
     ((-1 . (unsigned-byte 11)))
     -1
     nil
     nil
     (fp-opcode !fp-opcode))

    (xmmi
     (i x86)
     1
     ((-1 . (unsigned-byte 128)))
     -1
     nil
     nil
     (xmmi !xmmi))

    (mxcsr
     (x86)
     1
     ((-1 . (unsigned-byte 32)))
     -1
     nil
     nil
     (mxcsr !mxcsr))

    (msri
     (i x86)
     1
     ((-1 . (unsigned-byte 64)))
     -1
     nil
     nil
     (msri !msri))

    (ms
     (x86)
     0
     ((-1 . t))
     -1
     nil
     nil
     (ms !ms))

    (fault
     (x86)
     0
     ((-1 . t))
     -1
     nil
     nil
     (fault !fault))

    (env
     (x86)
     0
     ((-1 . env-alistp))
     -1
     nil
     nil
     (env !env))

    (undef
     (x86)
     0
     ((-1 . t))
     -1
     nil
     nil
     (undef !undef))

    ))

(defconst *x86-other-readers*
  '(

    (flgi
     (i x86)
     1
     ((-1 . n02p))
     -1
     nil
     ((:in-theory . ((:enable . (flgi)) (:disable . (rb wb)))))
     (flgi !flgi rflags !rflags))

    (rvm08
     (i x86)
     1
     ((0 . nil) ((1 . r) . n08p) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rvm08)))))
     (rvm08 !memi wvm08 wvm16 wvm32 wvm64 program-at))

    (rvm16
     (i x86)
     1
     ((0 . nil) ((1 . r) . n16p) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rvm16)))))
     (rvm16 !memi wvm08 wvm16 wvm32 wvm64 program-at))

    (rvm32
     (i x86)
     1
     ((0 . nil) ((1 . r) . n16p) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rvm32)))))
     (rvm32 !memi wvm08 wvm16 wvm32 wvm64 program-at))

    (rvm64
     (i x86)
     1
     ((0 . nil) ((1 . r) . n64p) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rvm64 rvm32)))))
     (rvm64 !memi wvm08 wvm16 wvm32 wvm64 program-at))

    (rm-low-64
     (i x86)
     1
     ((-1 . n64p))
     -1
     nil
     ((:in-theory . ((:enable . (rm-low-64 rm-low-32)))))
     (rm-low-64 rm-low-32 wm-low-64 wm-low-32 memi !memi wvm08 wvm16 wvm32
		wvm64 wm08 wm16 wm32 wm64 rm-size wm-size program-at))

    (rm-low-32
     (i x86)
     1
     ((-1 . n32p))
     -1
     nil
     ((:in-theory . ((:enable . (rm-low-32)))))
     (rm-low-32 rm-low-64 wm-low-32 wm-low-64 memi !memi wvm08 wvm16
		wvm32 wvm64 wm08 wm16 wm32 wm64 rm-size wm-size program-at))

    (rr08
     (i rex x86)
     1
     ((-1 . n08p))
     -1
     nil
     ((:in-theory . ((:enable . (rr08)))))
     (rr08 !rgfi wr08 wr16 wr32 wr64))

    (rr16
     (i x86)
     1
     ((-1 . n16p))
     -1
     nil
     ((:in-theory . ((:enable . (rr16)))))
     (rr16 !rgfi wr08 wr16 wr32 wr64))

    (rr32
     (i x86)
     1
     ((-1 . n32p))
     -1
     nil
     ((:in-theory . ((:enable . (rr32)))))
     (rr32 !rgfi wr08 wr16 wr32 wr64))

    (rr64
     (i x86)
     1
     ((-1 . n64p))
     -1
     nil
     ((:in-theory . ((:enable . (rr64 rr32)))))
     (rr64 !rgfi wr08 wr16 wr32 wr64))

    (read-x86-file-des
     (i x86)
     1
     ((-1 . t))
     -1
     nil
     ((:in-theory . ((:enable . (read-x86-file-des read-x86-file-des-logic)))))
     (read-x86-file-des write-x86-file-des env !env))

    (read-x86-file-contents
     (i x86)
     1
     ((-1 . t))
     -1
     nil
     ((:in-theory . ((:enable . (read-x86-file-contents read-x86-file-contents-logic)))))
     (read-x86-file-contents write-x86-file-contents env !env))

    ;; [Shilpi]: Note: the hypothesis for rb says that we're in
    ;; programmer-level mode.  So I still need theorems about rb when
    ;; we're in the system-level mode.

    ;; RB for the list of read bytes as the "main" return value
    (rb
     (addrs r-w-x x86)
     2
     ((0 . nil) ((1 . r) . true-listp) (2 . x86p))
     2
     (programmer-level-mode x86)
     ((:in-theory . ((:enable . (rm08)) (:disable . (wr08)))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode program-at))

    ;; RB for the error flag as the "main" return value
    (rb
     (addrs r-w-x x86)
     2
     (((0 . r) . t) (1 . true-listp) (2 . x86p))
     2
     (programmer-level-mode x86)
     ((:in-theory . ((:enable . (rm08)) (:disable . (wr08)))))
     (rb wb program-at memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32
	 wvm64 wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32
	 rm-low-64 rm-low-32 !programmer-level-mode programmer-level-mode)
     rb-error)

    ;; WB for the error flag as the "main" return value
    (wb
     (addr-bytes x86)
     1
     (((0 . r) . t) (1 . x86p))
     1
     (programmer-level-mode x86)
     ((:in-theory . ((:enable . (wm08)))))
     (wb rb !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08 wm16 wm32
	 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64 rm-low-32
	 !programmer-level-mode program-at)
     wb-error)

    (program-at
     (addrs bytes x86)
     2
     ((-1 . nil))
     -1
     (programmer-level-mode x86)
     ((:in-theory . ((:enable . (program-at)) (:disable . (rb)))))
     (program-at rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32
		 wvm64 wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32
		 rm-low-64 rm-low-32 !programmer-level-mode programmer-level-mode))

    ))


(defconst *x86-more-readers*
  '(

    ;; [Shilpi]: Note: (programmer-level-mode x86) doesn't appear as
    ;; an hypothesis here.

    ;; RM08 for the read byte as the "main" return value
    (rm08
     (addr r-w-x x86)
     2
     ((0 . nil) ((1 . r) . true-listp) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rm08)) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     rm08-top-level)

    ;; RM08 for the error as the "main" return value
    (rm08
     (addr r-w-x x86)
     2
     (((0 . r) . t) (1 . true-listp) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rm08)) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     rm08-error-top-level)

    ;; RB-1 for the list of read bytes as the "main" return value
    (rb-1
     (addrs r-w-x x86)
     2
     ((0 . nil) ((1 . r) . true-listp) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb rb-1 wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     rb-1-top-level)

    ;; RB-1 for the error flag as the "main" return value
    (rb-1
     (addrs r-w-x x86)
     2
     (((0 . r) . t) (1 . true-listp) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb rb-1 wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     rb-1-error-top-level)

    ;; RB for the list of read bytes as the "main" return value
    (rb
     (addrs r-w-x x86)
     2
     ((0 . nil) ((1 . r) . true-listp) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     rb-top-level)

    ;; RB for the error flag as the "main" return value
    (rb
     (addrs r-w-x x86)
     2
     (((0 . r) . t) (1 . true-listp) (2 . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     rb-error-top-level)

    ;; WB for the error flag as the "main" return value
    (wb
     (addr-bytes x86)
     1
     (((0 . r) . t) (1 . x86p))
     1
     nil
     ((:in-theory . ((:enable . (wm08)) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     wb-error-top-level)

    (program-at
     (addrs bytes x86)
     2
     ((-1 . nil))
     -1
     nil
     ((:in-theory . ((:enable . (program-at)) (:disable . (rb force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at msri !msri ctri !ctri)
     program-at-top-level)

    ))

;; ======================================================================

;; Writers:

(defconst *x86-state-primitive-writers*
  ;; Use J for the indices here.
  ;; Use a different val for every function.
  '(

    (!rgfi
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!rgfi rgfi rr08 rr16 rr32 rr64 !rgfi-size rgfi-size))


    (!rip
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!rip rip))


    (!rflags
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!rflags rflags flgi !flgi))


    (!memi
     (j v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!memi memi wvm08 wvm16 wvm32 wvm64 wm08 wm16 wm32 wm64 program-at))


    (!seg-visiblei
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!seg-visiblei seg-visiblei))

    (!seg-hiddeni
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!seg-hiddeni seg-hiddeni))

    (!stri
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!stri stri))


    (!ssr-visiblei
     (j v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!ssr-visiblei ssr-visiblei))

    (!ssr-hiddeni
     (j v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!ssr-hiddeni ssr-hiddeni))


    (!ctri
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!ctri ctri))


    (!dbgi
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!dbgi dbgi))


    (!fp-datai
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!fp-datai fp-datai))


    (!fp-ctrl
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (fp-ctrl !fp-ctrl))


    (!fp-status
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (fp-status !fp-status))


    (!fp-tag
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (fp-tag !fp-tag))


    (!fp-last-inst
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (fp-last-inst !fp-last-inst))


    (!fp-last-data
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (fp-last-data !fp-last-data))


    (!fp-opcode
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (fp-opcode !fp-opcode))

    (!xmmi
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!xmmi xmmi))

    (!mxcsr
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (mxcsr !mxcsr))


    (!msri
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     nil
     (!msri msri))


    (!ms
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!ms ms))


    (!fault
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!fault fault))


    (!env
     (v x86)
     0
     ((-1 . x86p))
     nil
     nil
     nil
     (!env env))


    (!undef
     (v x86)
     1
     ((-1 . x86p))
     nil
     nil
     nil
     (!undef undef))


    (!programmer-level-mode
     (v x86)
     0
     ((-1 . x86p))
     nil
     nil
     nil
     (!programmer-level-mode programmer-level-mode wb wm08 wm16 wm32 wm64
			     wm-size rb rm08 rm16 rm32 rm64 rm-size program-at))

    ))

(defconst *x86-other-writers*
  '(

    (!flgi
     (i v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (!flgi)) (:disable . (rb wb)))))
     (flgi !flgi rflags !rflags))

    (!flgi-undefined
     (flg x86)
     1
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (!flgi-undefined)))))
     (!flgi-undefined flgi !flgi rflags !rflags undef !undef))

    (wvm08
     (j v x86)
     2
     ((0 . nil) ((1 . w) . x86p))
     1
     nil
     ((:in-theory . ((:enable . (wvm08)))))
     (wvm08 !memi rvm08 rvm16 rvm32 rvm64 wvm16 wvm32 wvm64 program-at))


    (wvm16
     (j v x86)
     2
     ((0 . nil) ((1 . w) . x86p))
     1
     nil
     ((:in-theory . ((:enable . (wvm16)))))
     (wvm16 !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm32 wvm64 program-at))


    (wvm32
     (j v x86)
     2
     ((0 . nil) ((1 . w) . x86p))
     1
     nil
     ((:in-theory . ((:enable . (wvm32)))))
     (wvm32 !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm64 program-at))


    (wvm64
     (j v x86)
     2
     ((0 . nil) ((1 . w) . x86p))
     1
     nil
     ((:in-theory . ((:enable . (wvm64 wvm32)))))
     (wvm64 !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 program-at))


    (wm-low-64
     (addr v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (wm-low-64 wm-low-32)))))
     (wm-low-32 wm-low-64 memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64
		wm-size rm-size program-at))


    (wm-low-32
     (addr v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (wm-low-32)))))
     (wm-low-32 wm-low-64 memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64
		wm-size rm-size program-at))

    (ia32e-la-to-pa-page-table
     (lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86)
     8
     ((0 . nil) (1 . n52p) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . (ia32e-la-to-pa-page-table page-fault-exception page-fault-err-no)))))
     (fault !fault memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 program-at rm-low-32 rm-low-64 wm-low-32 wm-low-64 rb rb-1 wb wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 ia32e-la-to-pa-page-table ia32e-la-to-pa-page-directory ia32e-la-to-pa-page-dir-ptr-table ia32e-la-to-pa-pml4-table ia32e-la-to-pa))

    (ia32e-la-to-pa-page-directory
     (lin-addr base-addr wp smep nxe r-w-x cpl x86)
     7
     ((0 . nil) (1 . n52p) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . (ia32e-la-to-pa-page-directory page-fault-exception page-fault-err-no)))))
     (fault !fault memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 program-at rm-low-32 rm-low-64 wm-low-32 wm-low-64 rb rb-1 wb wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 ia32e-la-to-pa-page-table ia32e-la-to-pa-page-directory ia32e-la-to-pa-page-dir-ptr-table ia32e-la-to-pa-pml4-table ia32e-la-to-pa))


    (ia32e-la-to-pa-page-dir-ptr-table
     (lin-addr base-addr wp smep nxe r-w-x cpl x86)
     7
     ((0 . nil) (1 . n52p) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . (ia32e-la-to-pa-page-dir-ptr-table page-fault-exception page-fault-err-no)))))
     (fault !fault memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 program-at rm-low-32 rm-low-64 wm-low-32 wm-low-64 rb rb-1 wb wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 ia32e-la-to-pa-page-table ia32e-la-to-pa-page-directory ia32e-la-to-pa-page-dir-ptr-table ia32e-la-to-pa-pml4-table ia32e-la-to-pa))

    (ia32e-la-to-pa-pml4-table
     (lin-addr base-addr wp smep nxe r-w-x cpl x86)
     7
     ((0 . nil) (1 . n52p) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . (ia32e-la-to-pa-pml4-table page-fault-exception page-fault-err-no)))))
     (fault !fault memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 program-at rm-low-32 rm-low-64 wm-low-32 wm-low-64 rb rb-1 wb wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 ia32e-la-to-pa-page-table ia32e-la-to-pa-page-directory ia32e-la-to-pa-page-dir-ptr-table ia32e-la-to-pa-pml4-table ia32e-la-to-pa))

    (ia32e-la-to-pa
     (lin-addr r-w-x cpl x86)
     3
     ((0 . nil) (1 . n52p) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . (ia32e-la-to-pa page-fault-exception page-fault-err-no))
		     (:disable . (ia32e-la-to-pa-pml4-table ia32e-la-to-pa-page-dir-ptr-table ia32e-la-to-pa-page-directory ia32e-la-to-pa-page-table)))))
     (fault !fault memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 program-at rm-low-32 rm-low-64 wm-low-32 wm-low-64 rb rb-1 wb wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 ia32e-la-to-pa-page-table ia32e-la-to-pa-page-directory ia32e-la-to-pa-page-dir-ptr-table ia32e-la-to-pa-pml4-table ia32e-la-to-pa !ctri msri !msri))

    (wr08
     (j v rex x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (wr08)))))
     (wr08 !rgfi rr08 rr16 rr32 rr64 wr16 wr32 wr64 rgfi))


    (wr16
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (wr16)))))
     (wr16 !rgfi rr08 rr16 rr32 rr64 wr08 wr32 wr64 rgfi))


    (wr32
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (wr32)))))
     (wr32 !rgfi rr08 rr16 rr32 rr64 wr08 wr16 wr64 rgfi))


    (wr64
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (wr64 wr32)))))
     (wr64 !rgfi rr08 rr16 rr32 rr64 wr08 wr16 wr32 rgfi))


    (write-x86-file-des
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (write-x86-file-des write-x86-file-des-logic)))))
     (write-x86-file-des read-x86-file-des env !env))


    (write-x86-file-contents
     (j v x86)
     2
     ((-1 . x86p))
     nil
     nil
     ((:in-theory . ((:enable . (write-x86-file-contents write-x86-file-contents-logic)))))
     (write-x86-file-contents read-x86-file-contents env !env))

    ;; [Shilpi]: Note: the hypothesis for wb says that we're in
    ;; programmer-level mode.  So I still need theorems about wb when
    ;; we're in the system-level mode.

    (wb
     (addr-bytes x86)
     1
     ((0 . nil) ((1 . w) . x86p))
     1
     (programmer-level-mode x86)
     ((:in-theory . ((:enable . (wm08)))))
     (wb rb !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08 wm16
	 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64 rm-low-32
	 !programmer-level-mode))

    ))

(defconst *x86-more-writers*
  '(

    ;; [Shilpi]: Note: (programmer-level-mode x86) doesn't appear as
    ;; an hypothesis here.

    (rm08
     (addr r-w-x x86)
     2
     ((0 . nil) (1 . true-listp) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . (rm08)) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 program-at msri !msri fault !fault !programmer-level-mode)
     rm08-top-level)

    (rb-1
     (addrs r-w-x x86 acc)
     2
     ((0 . nil) (1 . true-listp) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb rb-1 wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode program-at fault !fault msri !msri)
     rb-1-top-level)

    ;; RB for the list of read bytes as the "main" return value
    (rb
     (addrs r-w-x x86)
     2
     ((0 . nil) (1 . true-listp) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb rb-1 wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode program-at fault !fault msri !msri)
     rb-top-level)

    ;; RB for the error flag as the "main" return value
    (rb
     (addrs r-w-x x86)
     2
     ((0 . t) (1 . true-listp) ((2 . w) . x86p))
     2
     nil
     ((:in-theory . ((:enable . ()) (:disable . (force (force))))))
     (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
	 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 !programmer-level-mode programmer-level-mode
	 program-at fault !fault msri !msri)
     rb-error-top-level)

    (wb
     (addr-bytes x86)
     1
     ((0 . nil) ((1 . w) . x86p))
     1
     nil
     ((:in-theory . ((:enable . (wm08)))))
     (wb rb rb-1 !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64
	 wm08 wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
	 rm-low-32 program-at !programmer-level-mode fault !fault msri !msri)
     wb-top-level)

    ;; (program-at
    ;;  (addrs bytes x86)
    ;;  2
    ;;  ((-1 . nil))
    ;;  -1
    ;;  nil
    ;;  ((:in-theory . ((:enable . (program-at)) (:disable . (rb force (force))))))
    ;;  (rb wb memi !memi rvm08 rvm16 rvm32 rvm64 wvm08 wvm16 wvm32 wvm64 wm08
    ;;      wm16 wm32 wm64 rm08 rm16 rm32 rm64 wm-low-64 wm-low-32 rm-low-64
    ;;      rm-low-32 !programmer-level-mode programmer-level-mode
    ;;      program-at msri !msri ctri !ctri)
    ;;  program-at-top-level)

    ))

;; ======================================================================

;; Some utilities for generating and manipulating sub-expressions:

(defun generate-unique-input-args (fn-name inputs)
  ;; This function allows us to avoid generating bad thms with the
  ;; following LHS
  ;; (rgfi i (!flgi i x86))
  ;; and generate
  ;; (rgfi rgfi-i (!flgi !flgi-i x86))
  ;; instead.  Note that x86 is left as it is.
  (if (endp inputs)
      nil
    (if (equal (car inputs) 'x86)
	(cons 'x86
	      (generate-unique-input-args fn-name (cdr inputs)))
      (cons (mk-name fn-name "-" (car inputs))
	    (generate-unique-input-args fn-name (cdr inputs))))))

(defun replace-arg-with-other-s
  ;; Example:
  ;; (replace-arg-with-other-s 'X86 '(I X86) '(MV-NTH 1 (WVM64 LIN-ADDR VAL X86)))
  (arg-to-replace input-list arg-to-be-replaced-with)

  (cond ((endp input-list) nil)
	(t (if (equal arg-to-replace (car input-list))
	       (cons arg-to-be-replaced-with (cdr input-list))
	     (cons (car input-list)
		   (replace-arg-with-other-s
		    arg-to-replace (cdr input-list)
		    arg-to-be-replaced-with))))))

(defun generate-proper-mv-nth-exp (pos-main-output func-call)
  ;; Example:
  ;; (generate-proper-mv-nth-exp 1 '(WVM64 LIN-ADDR VAL X86))
  (if (natp pos-main-output)
      `(mv-nth ,pos-main-output ,func-call)
    func-call))

(defun return-position-of-main-output (this-output-keys)
  ;; Example:
  ;; (return-position-of-main-output '((0 . NIL) ((1 . R) . N64P) (2 . X86P)))

  ;; TO-DO@Shilpi:
  ;; For now, we assume that there is only one "interesting" output of
  ;; a function.  E.g., rvm08 returns three arguments, and we care
  ;; only about the value read for our RoW proofs.

  (if (endp this-output-keys)
      -1
    (if (consp (car this-output-keys))
	(if (consp (caar this-output-keys))
	    (caaar this-output-keys)
	  (return-position-of-main-output
	   (cdr this-output-keys)))
      -1)))

(defun repeat-subexpression (count expression)
  (if (zp count)
      nil
    (cons expression
	  (repeat-subexpression (1- count) expression))))

(defun merge-in-theory-hints (this-hints that-hints)

  ;; Example:
  ;; (merge-in-theory-hints '((:IN-THEORY . ((:ENABLE . (RVM64 RVM32)))))
  ;;                        '((:IN-THEORY . ((:DISABLE . (WVM08))))))

  ;; TO-DO@Shilpi:
  ;; For now, we assume that the only hints we have for RoW and WoW
  ;; theorems are in-theory hints.

  (if (endp this-hints)
      (if (endp that-hints)
	  nil
	(let* ((enable
		(cdr (assoc :enable (cdr (assoc :in-theory
						that-hints)))))
	       (disable
		(cdr (assoc :disable (cdr (assoc :in-theory
						 that-hints))))))
	  `(:HINTS (("GOAL" :IN-THEORY (E/D ,ENABLE ,DISABLE))))))
    (if (endp that-hints)
	(let* ((enable
		(cdr (assoc :enable (cdr (assoc :in-theory
						this-hints)))))
	       (disable
		(cdr (assoc :disable (cdr (assoc :in-theory
						 this-hints))))))
	  `(:HINTS (("GOAL" :IN-THEORY (E/D ,ENABLE ,DISABLE)))))
      (let* ((this-enable
	      (cdr (assoc :enable (cdr (assoc :in-theory
					      this-hints)))))
	     (this-disable
	      (cdr (assoc :disable (cdr (assoc :in-theory
					       this-hints)))))
	     (that-enable
	      (cdr (assoc :enable (cdr (assoc :in-theory
					      that-hints)))))
	     (that-disable
	      (cdr (assoc :disable (cdr (assoc :in-theory
					       that-hints)))))
	     (enable  (append this-enable that-enable))
	     (disable (append this-disable that-disable)))
	`(:HINTS (("GOAL" :IN-THEORY (E/D ,ENABLE ,DISABLE))))))))

;; ======================================================================

;; A rule about update-nth...

(local
 (defthm update-nth-thm-2
   (implies (and (integerp i1)
		 (<= 0 i1)
		 (integerp i2)
		 (<= 0 i2)
		 (not (equal i1 i2)))
	    (equal (update-nth i2 v2 (update-nth i1 v1 x))
		   (update-nth i1 v1 (update-nth i2 v2 x))))))

;; ======================================================================

;; RoW theorems (inter-field):

(defun generate-inter-field-RoW-theorems-1 (this-field all-fields)
  ;; Example:
  ;; (generate-inter-field-RoW-theorems-1 (car *x86-state-primitive-readers*) *x86-state-primitive-writers*)
  (if (endp all-fields)
      nil
    (b* ( ;; THIS READER:
	 (this-name           (nth *pos-func-name*  this-field))
	 (alt-this-name       (or (nth *alt-name* this-field)
				  this-name))
	 (?this-inputs        (generate-unique-input-args
			       alt-this-name
			       (nth *pos-inputs*     this-field)))
	 (?this-input-x86     (nth *pos-input-x86*  this-field))
	 (?this-outputs       (nth *pos-outputs*    this-field))
	 (?this-output-x86    (nth *pos-output-x86* this-field))
	 (?this-hypotheses    (nth *pos-hypotheses* this-field))
	 (?this-hints         (nth *pos-hints*      this-field))
	 (?this-dont-pair     (nth *pos-dont-pair*  this-field))
	 (ret-this-output-pos (return-position-of-main-output this-outputs))

	 ;; THAT WRITER:
	 (that-field          (car all-fields))

	 (that-name           (nth *pos-func-name*  that-field))
	 (alt-that-name       (or (nth *alt-name* that-field)
				  that-name))
	 (?that-inputs        (generate-unique-input-args
			       alt-that-name
			       (nth *pos-inputs*     that-field)))
	 (?that-input-x86     (nth *pos-input-x86*  that-field))
	 (?that-outputs       (nth *pos-outputs*    that-field))
	 (?that-output-x86    (nth *pos-output-x86* that-field))
	 (?that-hypotheses    (nth *pos-hypotheses* that-field))
	 (?that-hints         (nth *pos-hints*      that-field))
	 (?that-dont-pair     (nth *pos-dont-pair*  that-field)))

	(if (or (member-equal this-name that-dont-pair)
		(member-equal that-name this-dont-pair))
	    (generate-inter-field-RoW-theorems-1 this-field (cdr all-fields))

	  (cons

	   (if (merge-in-theory-hints this-hints that-hints)
	       (append
		`(DEFTHM ,(mk-name alt-this-name "-" alt-that-name)
		   (implies ,(or (append this-hypotheses
					 that-hypotheses)
				 t)
			    (EQUAL ,(generate-proper-mv-nth-exp
				     ret-this-output-pos
				     (cons this-name
					   (replace-arg-with-other-s
					    'X86
					    this-inputs
					    (generate-proper-mv-nth-exp
					     that-output-x86
					     (cons that-name
						   that-inputs)))))
				   ,(generate-proper-mv-nth-exp
				     ret-this-output-pos
				     (cons this-name this-inputs)))))
		(merge-in-theory-hints this-hints that-hints))
	     `(DEFTHM ,(mk-name alt-this-name "-" alt-that-name)
		(implies ,(or (append this-hypotheses
				      that-hypotheses)
			      t)
			 (EQUAL ,(generate-proper-mv-nth-exp
				  ret-this-output-pos
				  (cons this-name
					(replace-arg-with-other-s
					 'X86
					 this-inputs
					 (generate-proper-mv-nth-exp
					  that-output-x86
					  (cons that-name
						that-inputs)))))
				,(generate-proper-mv-nth-exp
				  ret-this-output-pos
				  (cons this-name this-inputs))))))

	   (generate-inter-field-RoW-theorems-1 this-field (cdr all-fields)))))))

(defun generate-inter-field-RoW-theorems-fn (reader-fields writer-fields)
  ;; (generate-inter-field-RoW-theorems-fn *x86-state-primitive-readers* *x86-state-primitive-writers*)
  (if (endp reader-fields)
      nil
    (append (generate-inter-field-RoW-theorems-1 (car reader-fields)
						 writer-fields)
	    (generate-inter-field-RoW-theorems-fn (cdr reader-fields)
						  writer-fields))))

(defmacro generate-inter-field-RoW-theorems ()
  (cons 'progn
	(generate-inter-field-RoW-theorems-fn
	 *x86-state-primitive-readers*
	 *x86-state-primitive-writers*)))

(generate-inter-field-RoW-theorems)

;; ======================================================================

;; WoW theorems (inter-field):

(defun generate-inter-field-WoW-theorems-1 (this-field all-fields)
  ;; Example:
  ;; (generate-inter-field-WoW-theorems-1 (car *x86-state-primitive-writers*) *x86-state-primitive-writers*)
  (if (endp all-fields)
      nil
    (b* ( ;; THIS WRITER:
	 (this-name           (nth *pos-func-name*  this-field))
	 (alt-this-name       (or (nth *alt-name* this-field)
				  this-name))
	 (?this-inputs        (generate-unique-input-args
			       alt-this-name
			       (nth *pos-inputs*     this-field)))
	 (?this-input-x86     (nth *pos-input-x86*  this-field))
	 (?this-outputs       (nth *pos-outputs*    this-field))
	 (?this-output-x86    (nth *pos-output-x86* this-field))
	 (?this-hypotheses    (nth *pos-hypotheses* this-field))
	 (?this-hints         (nth *pos-hints*      this-field))
	 (?this-dont-pair     (nth *pos-dont-pair*  this-field))
	 (ret-this-output-pos (return-position-of-main-output
			       this-outputs))

	 ;; THAT WRITER:
	 (that-field          (car all-fields))

	 (that-name           (nth *pos-func-name*  that-field))
	 (alt-that-name       (or (nth *alt-name* that-field)
				  that-name))
	 (?that-inputs        (generate-unique-input-args
			       alt-that-name
			       (nth *pos-inputs*     that-field)))
	 (?that-input-x86     (nth *pos-input-x86*  that-field))
	 (?that-outputs       (nth *pos-outputs*    that-field))
	 (?that-output-x86    (nth *pos-output-x86* that-field))
	 (?that-hypotheses    (nth *pos-hypotheses* that-field))
	 (?that-hints         (nth *pos-hints*      that-field))
	 (?that-dont-pair     (nth *pos-dont-pair*  that-field))
	 (ret-that-output-pos (return-position-of-main-output
			       that-outputs)))

	(if (or (member-equal this-name that-dont-pair)
		(member-equal that-name this-dont-pair))
	    (generate-inter-field-WoW-theorems-1 this-field (cdr all-fields))

	  (cons

	   (if (merge-in-theory-hints that-hints this-hints)
	       (append
		`(DEFTHM ,(mk-name that-name "-" this-name)
		   (implies ,(or (append this-hypotheses
					 that-hypotheses)
				 t)
			    (EQUAL ,(generate-proper-mv-nth-exp
				     ret-that-output-pos
				     (cons that-name
					   (replace-arg-with-other-s
					    'X86
					    that-inputs
					    (generate-proper-mv-nth-exp
					     this-output-x86
					     (cons this-name
						   this-inputs)))))
				   ,(generate-proper-mv-nth-exp
				     ret-this-output-pos
				     (cons this-name
					   (replace-arg-with-other-s
					    'X86
					    this-inputs
					    (generate-proper-mv-nth-exp
					     that-output-x86
					     (cons that-name
						   that-inputs))))))))
		(merge-in-theory-hints that-hints this-hints))
	     `(DEFTHM ,(mk-name that-name "-" this-name)
		(implies ,(or (append this-hypotheses
				      that-hypotheses)
			      t)
			 (EQUAL ,(generate-proper-mv-nth-exp
				  ret-that-output-pos
				  (cons that-name
					(replace-arg-with-other-s
					 'X86
					 that-inputs
					 (generate-proper-mv-nth-exp
					  this-output-x86
					  (cons this-name
						this-inputs)))))
				,(generate-proper-mv-nth-exp
				  ret-this-output-pos
				  (cons this-name
					(replace-arg-with-other-s
					 'X86
					 this-inputs
					 (generate-proper-mv-nth-exp
					  that-output-x86
					  (cons that-name
						that-inputs)))))))))

	   (generate-inter-field-WoW-theorems-1 this-field (cdr all-fields)))

	  ))))

(defun generate-inter-field-WoW-theorems-fn (writer-fields)
  ;; (generate-inter-field-WoW-theorems *x86-state-primitive-writers*)
  (if (endp writer-fields)
      nil
    (append (generate-inter-field-WoW-theorems-1 (car writer-fields)
						 writer-fields)
	    (generate-inter-field-WoW-theorems-fn (cdr
						   writer-fields)))))

(defmacro generate-inter-field-WoW-theorems ()
  (cons 'progn
	(generate-inter-field-WoW-theorems-fn *x86-state-primitive-writers*)))

(generate-inter-field-WoW-theorems)

;; ======================================================================

(local
 (in-theory (e/d* ()
		  (abstract-stobj-fns-ruleset
		   memi !memi x86p
		   force (force)))))

(defmacro generate-field-and-user-mem-RoW-theorems ()
  (cons 'progn
	(append
	 (generate-inter-field-RoW-theorems-fn
	  *x86-state-primitive-readers*
	  *x86-other-writers*)
	 (generate-inter-field-RoW-theorems-fn
	  *x86-other-readers*
	  *x86-state-primitive-writers*)
	 (generate-inter-field-RoW-theorems-fn
	  *x86-other-readers*
	  *x86-other-writers*))))

(defmacro generate-field-and-user-mem-WoW-theorems ()
  (cons 'progn
	(generate-inter-field-WoW-theorems-fn
	 (append
	  ;; Always put the primitive functions at the top so that
	  ;; their updates appear outwards.
	  *x86-state-primitive-writers*
	  *x86-other-writers*))))

(generate-field-and-user-mem-RoW-theorems)

(local
 (in-theory (e/d (ia32e-la-to-pa-page-table
		  ia32e-la-to-pa-page-directory
		  ia32e-la-to-pa-page-dir-ptr-table
		  ia32e-la-to-pa-pml4-table
		  ia32e-la-to-pa)
		 ())))

(generate-field-and-user-mem-WoW-theorems)

(local
 (in-theory (e/d ()
		 (ia32e-la-to-pa-page-table
		  ia32e-la-to-pa-page-directory
		  ia32e-la-to-pa-page-dir-ptr-table
		  ia32e-la-to-pa-pml4-table
		  ia32e-la-to-pa))))

(defmacro generate-more-mem-RoW-theorems ()
  (cons 'progn
	(generate-inter-field-RoW-theorems-fn
	 *x86-state-primitive-readers*
	 *x86-more-writers*)))

(generate-more-mem-RoW-theorems)

;; ======================================================================

;; Misc. RoW/WoW theorems:

(defthm assoc-equal-put-assoc-equal-diff
  (equal (assoc-equal x (put-assoc-equal y z ss))
	 (if (equal x y)
	     (cons x z)
	   (assoc-equal x ss))))

(defthm assoc-equal-consp
  (implies (consp (assoc-equal x ss))
	   (consp (assoc-equal x (put-assoc-equal x z ss)))))

(defthm read-x86-file-des-write-x86-file-des-different-indices
  (implies (not (equal fd1 fd2))
	   (equal (read-x86-file-des fd1 (write-x86-file-des fd2 fd2-field x86))
		  (read-x86-file-des fd1 x86)))
  :hints (("Goal" :in-theory (e/d (read-x86-file-des
				   read-x86-file-des-logic
				   write-x86-file-des
				   write-x86-file-des-logic)
				  ()))))

(defthm read-x86-file-des-write-x86-file-des-same-indices
  (equal (read-x86-file-des fd (write-x86-file-des fd fd-field x86))
	 (cdr
	  (assoc-equal
	   fd
	   (put-assoc-equal fd fd-field
			    (cdr (assoc-equal :file-descriptors (env-read x86)))))))
  :hints (("Goal" :in-theory (e/d (read-x86-file-des
				   write-x86-file-des
				   read-x86-file-des-logic
				   write-x86-file-des-logic)
				  ()))))

(defthm read-x86-file-contents-write-x86-file-contents-same-indices
  (equal (read-x86-file-contents name (write-x86-file-contents name name-field x86))
	 (cdr
	  (assoc-equal
	   name
	   (put-assoc-equal name name-field
			    (cdr (assoc-equal :file-contents (env-read x86)))))))
  :hints (("Goal" :in-theory (e/d (read-x86-file-contents
				   write-x86-file-contents
				   read-x86-file-contents-logic
				   write-x86-file-contents-logic)
				  ()))))

(defthm read-x86-file-contents-write-x86-file-contents-different-indices
  (implies (not (equal name1 name2))
	   (equal (read-x86-file-contents name1 (write-x86-file-contents name2 name-field x86))
		  (read-x86-file-contents name1 x86)))
  :hints (("Goal" :in-theory (e/d (read-x86-file-contents
				   write-x86-file-contents
				   read-x86-file-contents-logic
				   write-x86-file-contents-logic)
				  ()))))

;; ======================================================================

;; Some rules about flgi and !flgi:

(local (include-book "centaur/gl/gl" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(include-book "centaur/bitops/equal-by-logbitp" :dir :system)

(encapsulate
 ()

 (local (in-theory (e/d () (unsigned-byte-p))))

 (local
  (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm unsigned-byte-p-and-logbitp
     (implies (and (unsigned-byte-p n x)
		   (natp m)
		   (<= n m))
	      (equal (logbitp m x) nil))
     :hints (("Goal" :in-theory (e/d* (ihsext-inductions
				       ihsext-recursive-redefs)
				      ()))))))

 (local
  (def-gl-thm flgi-!flgi-different-helper
    :hyp (unsigned-byte-p 32 rflags)
    :concl (equal (bitops::logsquash -11
				     (loghead 2 (logtail 12 rflags)))
		  (loghead 2 (logtail 12 rflags)))
    :g-bindings
    `((rflags (:g-number ,(gl-int 0 1 33))))))

 (defthm flgi-!flgi
   (implies (and (member i1 *flg-names*)
		 (member i2 *flg-names*)
		 (if (equal i2 *iopl*)
		     (unsigned-byte-p 2 v)
		   (unsigned-byte-p 1 v))
		 (x86p x86))
	    (equal (flgi i1 (!flgi i2 v x86))
		   (if (equal i1 i2) v (flgi i1 x86))))
   :hints (("Goal" :in-theory (e/d (flgi !flgi bool->bit) ()))))

 (local
  (def-gl-thm !flgi-!flgi-same-helper-1
    :hyp (and (unsigned-byte-p 32 rflags)
	      (unsigned-byte-p 32 y)
	      (equal y
		     (part-install 0 *2^32-1* :low x :width 1))
	      (member x *flg-names*)
	      (unsigned-byte-p 1 v1)
	      (unsigned-byte-p 1 v2))
    :concl (equal (logior (ash v2 x)
			  (logand y (logior (ash v1 x)
					    (logand y rflags))))
		  (logior (ash v2 x)
			  (logand y rflags)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
	   (:nat y 32))
     (:nat x 5)
     (:nat v1 2)
     (:nat v2 2))))

 (local
  (def-gl-thm !flgi-!flgi-same-helper-2
    :hyp (and (unsigned-byte-p 32 rflags)
	      (unsigned-byte-p 32 y)
	      (equal y
		     (part-install 0 *2^32-1* :low x :width 2))
	      (member x *flg-names*)
	      (unsigned-byte-p 2 v1)
	      (unsigned-byte-p 2 v2))
    :concl (equal (logior (ash v2 x)
			  (logand y (logior (ash v1 x)
					    (logand y rflags))))
		  (logior (ash v2 x)
			  (logand y rflags)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
	   (:nat y 32))
     (:nat x 5)
     (:nat v1 2)
     (:nat v2 2))))

 (defthm !flgi-!flgi-same
   (implies (and (member i *flg-names*)
		 (x86p x86))
	    (equal (!flgi i v2 (!flgi i v1 x86))
		   (!flgi i v2 x86)))
   :hints (("Goal" :in-theory (e/d (!flgi bool->bit) ()))))

 (local
  (def-gl-thm !flgi-!flgi-unequal-helper-1
    :hyp (and (unsigned-byte-p 32 rflags)
	      (unsigned-byte-p 32 yval)
	      (equal yval
		     (part-install 0 *2^32-1*
				   :low y
				   :width 1))
	      (member y *flg-names*)
	      (not (equal y *iopl*))
	      (< 0 y)
	      (unsigned-byte-p 1 v1)
	      (unsigned-byte-p 1 v2))
    :concl (equal
	    (logior (ash v2 y)
		    (logand yval
			    (logior v1 (bitops::logsquash 1 rflags))))
	    (logior v1 (ash v2 y)
		    (logand (1- yval)
			    (bitops::logsquash 1 rflags))))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
	   (:nat yval 32))
     (:nat y 5)
     (:mix (:nat v1 2)
	   (:nat v2 2)))))

 (local
  (def-gl-thm !flgi-!flgi-unequal-helper-2
    :hyp (and (unsigned-byte-p 32 rflags)
	      (unsigned-byte-p 32 xval)
	      (unsigned-byte-p 32 yval)
	      (equal xval
		     (part-install 0 *2^32-1*
				   :low x
				   :width (if (equal x *iopl*)
					      2
					    1)))
	      (equal yval
		     (part-install 0 *2^32-1*
				   :low y
				   :width (if (equal y *iopl*)
					      2
					    1)))
	      (member x *flg-names*)
	      (member y *flg-names*)
	      (not (equal x y))
	      (if (equal x *iopl*)
		  (unsigned-byte-p 2 v1)
		(unsigned-byte-p 1 v1))
	      (if (equal y *iopl*)
		  (unsigned-byte-p 2 v2)
		(unsigned-byte-p 1 v2)))
    :concl (equal (logior (ash v2 y)
			  (logand yval
				  (logior (ash v1 x)
					  (logand xval rflags))))
		  (logior (ash v1 x)
			  (logand xval
				  (logior (ash v2 y)
					  (logand yval rflags)))))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
	   (:nat xval 32)
	   (:nat yval 32))
     (:mix (:nat x 5)
	   (:nat y 5))
     (:mix (:nat v1 2)
	   (:nat v2 2)))))

 (local
  (def-gl-thm !flgi-!flgi-unequal-helper-3
    :hyp (and (unsigned-byte-p 32 rflags)
	      (unsigned-byte-p 1 v1)
	      (unsigned-byte-p 2 v2))
    :concl (equal (logior (ash v2 12)
			  (logand 4294955007
				  (logior v1
					  (bitops::logsquash 1 rflags))))
		  (logior v1 (ash v2 12)
			  (logand 4294955006
				  (bitops::logsquash 1 rflags))))
    :g-bindings
    (gl::auto-bindings
     (:nat rflags 32)
     (:mix (:nat v1 2)
	   (:nat v2 2)))))

 (defthm !flgi-!flgi-different-unequal-indices
   (implies (and (not (equal i1 i2))
		 (member i1 *flg-names*)
		 (member i2 *flg-names*)
		 (x86p x86))
	    (equal (!flgi i2 v2 (!flgi i1 v1 x86))
		   (!flgi i1 v1 (!flgi i2 v2 x86))))
   :hints (("Goal" :in-theory (e/d (!flgi bool->bit) ())))
   :rule-classes ((:rewrite :loop-stopper ((i2 i1)))))

 (defthm !flgi-!flgi-different-concrete-indices
   (implies (and (syntaxp (quotep i1))
		 (syntaxp (quotep i2))
		 (member i1 *flg-names*)
		 (member i2 *flg-names*)
		 (x86p x86))
	    (equal (!flgi i2 v2 (!flgi i1 v1 x86))
		   (if (< i1 i2)
		       (!flgi i1 v1 (!flgi i2 v2 x86))
		     (!flgi i2 v2 (!flgi i1 v1 x86)))))
   :rule-classes ((:rewrite :loop-stopper ((i2 i1)))))

 (local
  (def-gl-thm !flgi-flgi-helper-1
    :hyp (unsigned-byte-p 32 rflags)
    :concl (equal (logior (logand 4294955007 rflags)
			  (ash (loghead 2 (logtail 12 rflags))
			       12))
		  rflags)
    :g-bindings
    (gl::auto-bindings
     (:nat rflags 32))))

 (local
  (defthm unsigned-byte-p-not-logbitp-and-logand
    (implies (and (unsigned-byte-p 32 x)
		  (not (logbitp m x))
		  (equal mval
			 (part-install 0 *2^32-1*
				       :low m
				       :width 1)))
	     (equal (logand mval x) x))
    :hints ((and stable-under-simplificationp
		 (bitops::equal-by-logbitp-hint)))))

 (local
  (defthm unsigned-byte-p-not-logbitp-and-logsquash
    (implies (and (unsigned-byte-p 32 x)
		  (not (logbitp 0 x)))
	     (equal (bitops::logsquash 1 x) x))
    :hints (("Goal" :in-theory (e/d* (ihsext-inductions
				      ihsext-recursive-redefs)
				     ())))))

 (local
  (defthm unsigned-byte-p-logbitp-and-logsquash
    (implies (and (unsigned-byte-p 32 x)
		  (logbitp 0 x))
	     (equal (logior 1 (bitops::logsquash 1 x)) x))
    :hints (("Goal" :in-theory (e/d* (ihsext-inductions
				      ihsext-recursive-redefs)
				     ())))))

 (local
  (defthmd unsigned-byte-p-logbitp-and-logand-helper-1
    (implies (and (unsigned-byte-p 32 x)
		  (natp m)
		  (logbitp m x)
		  (equal mval1
			 (part-install 0 *2^32-1*
				       :low m
				       :width 1))
		  (equal mval2 (ash 1 m)))
	     (equal (logior mval2 (logand mval1 x))
		    (logand (logior mval2 mval1) x)))
    :hints (("Goal" :in-theory (e/d (bool->bit b-ior b-and) ()))
	    (and stable-under-simplificationp
		 (bitops::equal-by-logbitp-hint)))))

 (local
  (defthmd unsigned-byte-p-logbitp-and-logand-helper-2
    (implies (and (unsigned-byte-p 32 x)
		  (natp m)
		  (logbitp m x)
		  (equal mval1
			 (part-install 0 *2^32-1*
				       :low m
				       :width 1))
		  (equal mval2 (ash 1 m)))
	     (equal (logand (logior mval2 mval1) x)
		    x))
    :hints (("Goal" :in-theory (e/d (bool->bit b-ior b-and) ()))
	    (and stable-under-simplificationp
		 (bitops::equal-by-logbitp-hint)))))

 (local
  (defthm unsigned-byte-p-logbitp-and-logand
    (implies (and
	      ;; Since m is a free variable, I've put the logbitp
	      ;; hypothesis at the top to help ACL2 do matching
	      ;; effectively.  Moving this hyp to a lower position will
	      ;; reduce the applicability of this rule.
	      (logbitp m x)
	      (syntaxp (quotep mval1))
	      (syntaxp (quotep mval2))
	      (unsigned-byte-p 32 x)
	      (natp m)
	      (equal mval1
		     (part-install 0 *2^32-1*
				   :low m
				   :width 1))
	      (equal mval2 (ash 1 m)))
	     (equal (logior mval2 (logand mval1 x))
		    x))
    :hints (("Goal" :use (unsigned-byte-p-logbitp-and-logand-helper-1
			  unsigned-byte-p-logbitp-and-logand-helper-2)))))

 (defthmd !flgi-flgi
   (implies (and (equal x (flgi i x86))
		 (member i *flg-names*)
		 (x86p x86))
	    (equal (!flgi i x x86) x86))
   :hints (("Goal" :in-theory
	    (e/d
	     (flgi !flgi bool->bit !rflags-rflags)
	     (member-equal (member-equal))))))

 ) ;; End of encapsulate

;; ======================================================================

;; Some meta rules here:

;; A meta rule about get-all-rflags that removes all the writes to the state
;; that do not affect the value of get-all-rflags: I should extend the
;; evaluator to more functions.

;; (defevaluator get-all-rflags-evl get-all-rflags-evl-list
;;   ((get-all-rflags x86)
;;    (!flgi i v x86)
;;    (!rgfi i v x86)
;;    (!rip v x86)
;;    (if x y z)
;;    (mv-nth i x)
;;    (wb addr-lst x86)
;;    (programmer-level-mode x86)
;;    ))

;; (local
;;  (include-book "std/lists/take" :dir :system))

;; (defun remove-subterm-after-!flgi (get-all-rflags-arg)

;;   ;; (remove-subterm-after-!flgi '(!flgi i v (!flgi i x (!rgfi i v x86))))
;;   ;; (remove-subterm-after-!flgi '(!rgfi i v x86))
;;   ;; (remove-subterm-after-!flgi '(!flgi i v x86))
;;   ;; (remove-subterm-after-!flgi '(!rip v x86))
;;   ;; (remove-subterm-after-!flgi '(!flgi i v (!rip x (mv-nth '1 (wb addr-lst x86)))))

;;   (declare (xargs :guard (pseudo-termp get-all-rflags-arg)))
;;   (if (atom get-all-rflags-arg)
;;       get-all-rflags-arg
;;     (if (equal (car get-all-rflags-arg) '!flgi)
;;         ;; (take 3 '(!flgi 1 0 x86))
;;         (append (take 3 get-all-rflags-arg)
;;                 (list (remove-subterm-after-!flgi (cadddr get-all-rflags-arg))))
;;       (if (equal (car get-all-rflags-arg) '!rip)
;;           ;; (cadddr '(!rip v x86))
;;           (remove-subterm-after-!flgi (caddr get-all-rflags-arg))
;;         (if (equal (car get-all-rflags-arg) '!rgfi)
;;             ;; (cadddr '(!rgfi i v x86))
;;             (remove-subterm-after-!flgi (cadddr get-all-rflags-arg))
;;           (if (and (equal (car get-all-rflags-arg) 'mv-nth)
;;                    ;; Need to quote this number...
;;                    (equal (cadr get-all-rflags-arg) ''1)
;;                    (consp (caddr get-all-rflags-arg))
;;                    (equal (caaddr get-all-rflags-arg) 'wb))
;;               ;; (cadr (cdaddr '(mv-nth 1 (wb addr-lst x86))))
;;               (remove-subterm-after-!flgi (cadr (cdaddr get-all-rflags-arg)))
;;             get-all-rflags-arg))))))

;; (defun get-all-rflags-meta-fn (term)
;;   ;; (get-all-rflags-meta-fn '(get-all-rflags (!flgi i v (!flgi i x (!rgfi i v x86)))))
;;   ;; (get-all-rflags-meta-fn '(get-all-rflags (!flgi i v (!flgi i x x86))))
;;   ;; (get-all-rflags-meta-fn '(get-all-rflags x86))
;;   ;; (get-all-rflags-meta-fn '(get-all-rflags (!flgi i v (!rip x (mv-nth '1 (wb addr-lst x86))))))
;;   (declare (xargs :guard (pseudo-termp term)))
;;   (if (and (consp term)
;;            (equal (length term) 2)
;;            (equal (car term) 'get-all-rflags))
;;       (cons (car term)
;;             (list (remove-subterm-after-!flgi (cadr term))))
;;     term))

;; (defun hyp-get-all-rflags-meta-fn (term )
;;   ;; (hyp-get-all-rflags-meta-fn '(get-all-rflags (!flgi i v (!flgi i x (!rgfi i v x86)))))
;;   ;; (hyp-get-all-rflags-meta-fn '(get-all-rflags (!flgi i v (!flgi i x x86))))
;;   ;; (hyp-get-all-rflags-meta-fn '(get-all-rflags x86))
;;   (declare (xargs :guard (pseudo-termp term)))
;;   (if (and (consp term)
;;            (equal (length term) 2)
;;            (equal (car term) 'get-all-rflags))
;;       (cons 'programmer-level-mode
;;             (list (remove-subterm-after-!flgi (cadr term))))
;;     term))

;; (local
;;  (include-book "std/lists/append" :dir :system))

;; (defthm programmer-level-mode-remove-subterm-after-!programmer-level-mode
;;   (implies (programmer-level-mode (get-all-rflags-evl (remove-subterm-after-!flgi term) a))
;;            (equal (programmer-level-mode
;;                    (get-all-rflags-evl (remove-subterm-after-!flgi term) a))
;;                   (programmer-level-mode (get-all-rflags-evl term a)))))

;; (defthm flgi-remove-subterm-after-!flgi
;;   (implies (programmer-level-mode (get-all-rflags-evl (remove-subterm-after-!flgi term) a))
;;            (equal (flgi i (get-all-rflags-evl (remove-subterm-after-!flgi term) a))
;;                   (flgi i (get-all-rflags-evl term a))))
;;   :hints (("Subgoal *1/9" :in-theory
;;            (e/d ()
;;                 (flgi-wb
;;                  programmer-level-mode-remove-subterm-after-!programmer-level-mode))
;;            :use ((:instance flgi-wb
;;                             (x86 (get-all-rflags-evl (caddar (cddr term)) a))
;;                             (i i)
;;                             (wb-addr-bytes (get-all-rflags-evl (cadadr (cdr term)) a)))
;;                  (:instance programmer-level-mode-remove-subterm-after-!programmer-level-mode
;;                             (term (caddar (cddr term)))
;;                             (a a))))))

;; (defthm get-all-rflags-remove-fluff-writes-meta-lemma
;;   (implies (get-all-rflags-evl (hyp-get-all-rflags-meta-fn term) a)
;;            (equal (get-all-rflags-evl term a)
;;                   (get-all-rflags-evl (get-all-rflags-meta-fn term) a)))
;;   :hints (("Goal" :in-theory (e/d (get-all-rflags) (force (force)))))
;;   :rule-classes ((:meta :trigger-fns (get-all-rflags))))

;; ----------------------------------------------------------------------

;; Making some functions untouchable after proving RoW/WoW thms about
;; them:

(push-untouchable (
		   ;; Accessors
		   env
		   env$a
		   env$c
		   env-read-logic
		   env-write-logic
		   read-x86-file-des-logic
		   read-x86-file-contents-logic
		   ;; Updaters
		   !env
		   !env$a
		   !env$c
		   write-x86-file-des-logic
		   delete-x86-file-des-logic
		   write-x86-file-contents-logic
		   delete-x86-file-contents-logic
		   pop-x86-oracle-logic
		   !undef
		   )
		  t)

;; ======================================================================
