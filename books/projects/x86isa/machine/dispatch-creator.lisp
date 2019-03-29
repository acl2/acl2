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

(defsection dispatch-creator
  :parents (filtering-instructions)
  :short "Utilities to generate opcode dispatch functions from the annotated
opcode maps."
  )

(local (xdoc::set-default-parents 'dispatch-creator))

;; ----------------------------------------------------------------------

(local
 (defthm true-listp-of-subst-when-not-true-listp-old
   (implies (and (true-listp tree)
                 (not (true-listp old)))
            (true-listp (acl2::subst new old tree)))))


(define replace-formals-with-arguments-aux ((bindings eqlable-alistp)
                                            (formals true-listp))
  (if (endp bindings)
      formals
    (b* ((binding     (car bindings))
         (formal      (car binding))
         ((unless (not (true-listp formal)))
          (er hard? 'replace-formals-with-arguments-aux
              "~%Formal ~p0 not expected to be a true-list!~%"
              formal))
         (argument    (cdr binding))
         (new-formals (acl2::subst argument formal formals)))
      (replace-formals-with-arguments-aux (cdr bindings) new-formals)))
  ///
  (defthm true-listp-of-replace-formals-with-arguments-aux
    (implies (true-listp formals)
             (true-listp (replace-formals-with-arguments-aux
                          bindings formals)))))

(define replace-formals-with-arguments ((fn symbolp)
                                        (bindings eqlable-alistp)
                                        (world plist-worldp))

  (b* ((formals (acl2::formals fn world))
       ((unless (true-listp formals)) nil)
       (args    (replace-formals-with-arguments-aux bindings formals))
       (call    (cons fn args)))
    call)
  ///
  (defthm true-listp-of-replace-formals-with-arguments
    (true-listp (replace-formals-with-arguments fn bindings world))))

(define create-exceptions-check ((exc exception-desc-p))
  ;; (create-exceptions-check '((:UD (UD-LOCK-USED))))
  ;; (create-exceptions-check '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
  ;; (create-exceptions-check '((:ud  . ((ud-not-in-prot-or-64-mode)
  ;;                                     (ud-not-in-vmx-operation)
  ;;                                     (ud-invept-not-supported)
  ;;                                     (ud-ModR/M.Mod-indicates-Register)))
  ;;                            (:ex . (chk-exc :type-4 nil))))
  :guard-hints (("Goal" :in-theory (e/d (exception-desc-p) ())))
  (if (atom exc) nil
    (b* ((exception (caar exc))
         (exception-list (cdar exc)))
      (if (eq exception :ex)
          `(let ((chk-ex (or ,@exception-list)))
             (or chk-ex
                 ,(create-exceptions-check (cdr exc))))
        `(if (or ,@exception-list) (quote ,exception)
           ,(create-exceptions-check (cdr exc)))))))

(define make-exception-handling-cases ((exception-info exception-desc-p)
                                       illegal unimplemented
                                       (world plist-worldp))
  :prepwork ((local (in-theory (e/d (exception-desc-p) ()))))
  (append (and (or (assoc :ud exception-info)
                   (assoc :ex exception-info))
               (list (list :ud illegal)))
          (and (or (assoc :gp exception-info)
                   (assoc :ex exception-info))
               (list (list :gp (replace-formals-with-arguments
                                'x86-general-protection
                                '((message . "#GP Encountered!"))
                                world))))
          (and (or (assoc :nm exception-info)
                   (assoc :ex exception-info))
               (list (list :nm (replace-formals-with-arguments
                                'x86-device-not-available
                                '((message . "#NM Encountered!"))
                                world))))
          (list (list t unimplemented))))

(define create-call-from-fn-and-exception ((fn fn-desc-p)
                                           (exc exception-desc-p)
                                           (feat symbol-listp)
                                           (wrld plist-worldp))
  :prepwork ((local (in-theory (e/d (exception-desc-p fn-desc-p) ()))))

  (b* ((unimplemented-opcode  (replace-formals-with-arguments
                               'x86-step-unimplemented
                               '((message . "Opcode Unimplemented in x86isa!"))
                               wrld))
       (unimplemented-exc  (replace-formals-with-arguments
                            'x86-step-unimplemented
                            '((message . "Unimplemented exception in x86isa!"))
                            wrld))
       (illegal          (replace-formals-with-arguments
                          'x86-illegal-instruction
                          '((message . "#UD Encountered!"))
                          wrld))
       (fn-call          (if (equal fn nil)
                             unimplemented-opcode
                           (let ((fn-name (car fn))
                                 (bindings (cdr fn)))
                             (if (equal fn-name :no-instruction)
                                 illegal
                               (replace-formals-with-arguments
                                fn-name bindings wrld)))))
       ;; new-exc explicitly accounts for feature flag information too.
       (new-exc          (if feat
                             (b* ((ud (cdr (assoc :ud exc)))
                                  (feat+ud
                                   (cons `(equal (feature-flags-macro ',feat) 0)
                                         ud)))
                               (put-assoc :ud feat+ud exc))
                           exc))
       (exception-check  (create-exceptions-check new-exc))
       (exception-cases  (make-exception-handling-cases
                          new-exc illegal unimplemented-exc wrld)))
    (cond ((equal fn nil)
           (if exception-check
               `(let ((fault-var ,exception-check))
                  (if fault-var (case fault-var ,@exception-cases)
                    ,fn-call))
             fn-call))
          (t
           (if exception-check
               `(let ((fault-var ,exception-check))
                  (if fault-var
                      (case fault-var ,@exception-cases)
                    ,fn-call))
             fn-call)))))

(define vex-keyword-case-gen ((prefix-case keywordp))

  (case prefix-case
    (:UNUSED-VVVV     `((equal (vex->vvvv vex-prefixes) #b1111)))
    ((:NDS :NDD :DDS) `((not (equal (vex->vvvv vex-prefixes) #b1111))))
    ((:128 :LZ :L0)   `((equal (vex->l vex-prefixes) 0)))
    ((:256 :L1)       `((equal (vex->l vex-prefixes) 1)))
    ((:no-prefix)     `((equal (vex->pp vex-prefixes) 0)))
    ((:66)            `((equal (vex->pp vex-prefixes) #.*v66*)))
    ((:F3)            `((equal (vex->pp vex-prefixes) #.*vF3*)))
    ((:F2)            `((equal (vex->pp vex-prefixes) #.*vF2*)))
    ((:W0)            `((equal (vex->w vex-prefixes) 0)))
    ((:W1)            `((equal (vex->w vex-prefixes) 1)))
    ;; I don't need :0F, :0F38, and :0F3A below because the
    ;; vex-decode-and-execute function deals with this already.
    ;; ((:0F)            `((vex-prefixes-map-p #x0F vex-prefixes)))
    ;; ((:0F38)          `((vex-prefixes-map-p #x0F38 vex-prefixes)))
    ;; ((:0F3A)          `((vex-prefixes-map-p #x0F3A vex-prefixes)))
    (otherwise
     ;; :LIG, :WIG, :VEX, etc.
     `())))

(define evex-keyword-case-gen ((prefix-case keywordp))

  (case prefix-case
    (:UNUSED-VVVV     `((and (equal (evex->vvvv evex-prefixes) #b1111)
                             (equal (evex->v-prime evex-prefixes) #b1))))
    ((:NDS :NDD :DDS) `((not
                         (and (equal (evex->vvvv evex-prefixes) #b1111)
                              (equal (evex->v-prime evex-prefixes) #b1)))))
    ((:128 :LZ :L0)   `((equal (evex->vl/rc evex-prefixes) 0)))
    ((:256 :L1)       `((equal (evex->vl/rc evex-prefixes) 1)))
    (:512             `((equal (evex->vl/rc evex-prefixes) 2)))
    ((:no-prefix)     `((equal (evex->pp evex-prefixes) 0)))
    ((:66)            `((equal (evex->pp evex-prefixes) #.*v66*)))
    ((:F3)            `((equal (evex->pp evex-prefixes) #.*vF3*)))
    ((:F2)            `((equal (evex->pp evex-prefixes) #.*vF2*)))
    ((:W0)            `((equal (evex->w evex-prefixes) 0)))
    ((:W1)            `((equal (evex->w evex-prefixes) 1)))
    ;; I don't need to account for :0F, :0F38, and :0F3A because the
    ;; evex-decode-and-execute function deals with this already.
    (otherwise
     ;; :LIG, :WIG, :EVEX, etc.
     `())))

(define avx-keyword-case-gen ((prefix-case keywordp)
                              (vex? booleanp))
  (if vex?
      (vex-keyword-case-gen prefix-case)
    (evex-keyword-case-gen prefix-case)))

(define avx-opcode-case-gen-aux ((case-info acl2::keyword-listp)
                                 (vex? booleanp))
  (if (endp case-info)
      nil
    `(,@(avx-keyword-case-gen (car case-info) vex?)
      ,@(avx-opcode-case-gen-aux (cdr case-info) vex?))))

(local
 (defthm subsetp-equal-and-keyword-listp
   (implies (and (subsetp-equal x y)
                 (acl2::keyword-listp y)
                 (true-listp x))
            (acl2::keyword-listp x))
   :hints (("Goal" :in-theory (e/d (subsetp-equal
                                    acl2::keyword-listp)
                                   ())))))

(local
 (defthm cons-keyword-listp
   (implies (and (keywordp e)
                 (acl2::keyword-listp x))
            (acl2::keyword-listp (cons e x)))
   :hints (("Goal" :in-theory (e/d (acl2::keyword-listp) ())))))

(define create-dispatch-for-avx-opcode ((map-key keywordp)
                                        (inst inst-p)
                                        call
                                        (caseStmt true-listp)
                                        rest)
  :guard (member-equal
          map-key
          '(:vex-0F :vex-0F-38 :vex-0F-3A
                    :evex-0F :evex-0F-38 :evex-0F-3A))

  (b* (((inst inst))
       (opcode inst.opcode)
       ((opcode opcode))
       (vex? (and (or
                   (eql map-key :vex-0F)
                   (eql map-key :vex-0F-38)
                   (eql map-key :vex-0F-3A))
                  opcode.vex
                  (eql opcode.evex nil)))
       (evex? (and (or
                    (eql map-key :evex-0F)
                    (eql map-key :evex-0F-38)
                    (eql map-key :evex-0F-3A))
                   (eql opcode.vex nil)
                   opcode.evex))
       ((unless (or vex? evex?)) rest)
       ;; (- (cw "~% vex: ~p0 vex?: ~p1~%" opcode.vex vex?))
       ;; (- (cw "~% evex: ~p0 evex?: ~p1 ~%" opcode.evex evex?))
       (avx (if vex? opcode.vex opcode.evex))
       (prefix (cond ((member-equal :66 avx) :66)
                     ((member-equal :F2 avx) :F2)
                     ((member-equal :F3 avx) :F3)
                     (t :no-prefix)))
       (avx (if (equal prefix :no-prefix)
                (cons :no-prefix avx)
              avx))
       (avx (if (or (member-equal :NDS avx)
                    (member-equal :NDD avx)
                    (member-equal :DDS avx))
                avx
              (cons :UNUSED-VVVV avx)))
       ;; (- (cw "~% avx: ~p0 ~%" avx))
       (avxCaseStmt
        (avx-opcode-case-gen-aux avx vex?))
       ;; (- (cw "~% avxCaseStmt: ~p0 ~%" avxCaseStmt))
       (newCaseStmt
        (append avxCaseStmt (list caseStmt)))
       ;; (- (cw "~% newCaseStmt: ~p0 ~%" newCaseStmt))
       (newCaseStmt (if (acl2::all-equalp nil newCaseStmt)
                        nil
                      (if (< 1 (len (remove-equal 'nil newCaseStmt)))
                          `(and ,@newCaseStmt)
                        newCaseStmt))))
    (if newCaseStmt
        (cons `(,newCaseStmt ,call) rest)
      call)))

(define create-dispatch-for-one-opcode ((inst-lst inst-list-p)
                                        (map-key  keywordp)
                                        (wrld plist-worldp))

  ;; (create-dispatch-for-one-opcode
  ;;  (select-insts *one-byte-opcode-map* :opcode #x0)
  ;;  :one-byte
  ;;  (w state))

  ;; (create-dispatch-for-one-opcode
  ;;  (select-insts *one-byte-opcode-map* :opcode #x80)
  ;;  :one-byte
  ;;  (w state))

  :guard (member-equal
          map-key
          '(:one-byte
            :two-byte
            :0F-38-three-byte
            :0F-3A-three-byte
            :vex-0F :vex-0F-38 :vex-0F-3A
            :evex-0F :evex-0F-38 :evex-0F-3A))

  :guard-hints (("Goal"
                 :in-theory
                 (e/d ()
                      (acl2::member-of-cons
                       endp
                       keywordp
                       acl2::keyword-listp
                       len
                       remove-equal
                       member-equal
                       atom
                       not
                       acl2::symbolp-of-car-when-symbol-listp
                       symbol-listp
                       (tau-system)))))

  (b* (((when (atom inst-lst))
        (mv t
            `((t ,(replace-formals-with-arguments
                   'x86-illegal-instruction
                   '((message . "#UD Encountered!"))
                   wrld)))))
       (inst (car inst-lst))
       ((inst inst))
       (opcode inst.opcode)
       ((opcode opcode))
       ((when (and opcode.vex opcode.evex))
        (mv nil
            (er hard? 'create-dispatch-for-one-opcode
                "Both vex and evex?! Couldn't create dispatch for ~p0.~%" inst)))
       (caseStmt
         `(,@(and opcode.mode
                  (if (eql opcode.mode :o64)
                      `((equal proc-mode #.*64-bit-mode*))
                    `((not (equal proc-mode #.*64-bit-mode*)))))
           ;; opcode.feat is accounted for in
           ;; create-call-from-fn-and-exception.
           ;; ,@(and opcode.feat
           ;;        `((equal (feature-flags-macro ',opcode.feat) 1)))
           ,@(and opcode.reg
                  `((equal (modr/m->reg modr/m) ,opcode.reg)))
           ,@(and opcode.mod
                  (if (equal opcode.mod :mem)
                      `((not (equal (modr/m->mod modr/m) #b11)))
                    `((equal (modr/m->mod modr/m) ,opcode.mod))))
           ,@(and opcode.r/m
                  `((equal (modr/m->r/m modr/m) ,opcode.r/m)))
           ,@(and opcode.pfx
                  `((equal mandatory-prefix
                           ,(case opcode.pfx
                              (:66        #x66)
                              (:F2        #xF2)
                              (:F3        #xF3)
                              (otherwise  #x0)))))
           ,@(and opcode.rex
                  ;; :w and :not-w are the only two REX-based conditions right
                  ;; now.
                  (if (equal opcode.rex :w)
                      `((logbitp #.*w* rex-byte))
                    `((not (logbitp #.*w* rex-byte)))))))
       (caseStmt
         (if (acl2::all-equalp nil caseStmt)
             nil
           (if (< 1 (len (remove-equal 'nil caseStmt)))
               `(and ,@caseStmt)
             ;; Remove the final nil.
             (car caseStmt))))
       (call (create-call-from-fn-and-exception
              inst.fn inst.excep opcode.feat wrld))
       ((mv & rest)
        (create-dispatch-for-one-opcode (cdr inst-lst) map-key wrld))
       ((when (and (member-equal
                    map-key
                    '(:vex-0F :vex-0F-38 :vex-0F-3A
                              :evex-0F :evex-0F-38 :evex-0F-3A))
                   (or opcode.vex opcode.evex)))
        (mv t
            (create-dispatch-for-avx-opcode
             map-key inst call caseStmt rest)))
       ((when (or (eql map-key :one-byte)
                  (eql map-key :two-byte)
                  (eql map-key :0F-38-three-byte)
                  (eql map-key :0F-3A-three-byte)))
        (if caseStmt
            (mv t (cons `(,caseStmt ,call) rest))
          ;; This better be the last inst.
          (if (endp (cdr inst-lst))
              (mv nil call)
            (mv nil
                (er hard? 'create-dispatch-for-one-opcode
                    "~% Expected this to be the last inst, but it's not! ~
                    These insts are left: ~% ~p0"
                    (cdr inst-lst)))))))
    ;; Unreachable.
    (mv nil nil)))

(define create-dispatch-for-opcodes ((first-opcode 24bits-p)
                                     (num-opcodes  natp)
                                     (map-key  keywordp)
                                     (wrld plist-worldp))

  ;; Include the following for debugging the events that generate the dispatch
  ;; functions:
  ;; (local (include-book "instructions/top" :ttags :all))
  ;; (local (include-book "dispatch-macros"))

  ;; (create-dispatch-for-opcodes     #ux0F_00 256 :two-byte (w state))
  ;; (create-dispatch-for-opcodes        #ux00 256 :one-byte (w state))
  ;; (create-dispatch-for-opcodes  #ux0F_38_00 256 :0F-38-three-byte (w state))
  ;; (create-dispatch-for-opcodes  #ux0F_3A_00 256 :0F-3A-three-byte (w state))

  :guard (member-equal
          map-key
          '(:one-byte
            :two-byte
            :0F-38-three-byte
            :0F-3A-three-byte
            :vex-0F :vex-0F-38 :vex-0F-3A
            :evex-0F :evex-0F-38 :evex-0F-3A))

  (b* (((when (zp num-opcodes))
        `((t
           ,(replace-formals-with-arguments
             'x86-illegal-instruction
             '((message . "#UD Encountered!"))
             wrld))))
       (rest (if (24bits-p (1+ first-opcode))
                 (create-dispatch-for-opcodes
                  (1+ first-opcode) (1- num-opcodes) map-key wrld)
               (er hard? 'create-dispatch-for-opcodes
                   "Illegal opcode ~s0.~%" (str::hexify (1+ first-opcode)))))
       (map (select-opcode-map map-key))
       (same-opcode-insts (select-insts map :opcode first-opcode))
       (relevant-insts
        (if (member-equal map-key '(:one-byte
                                    :two-byte
                                    :0F-38-three-byte
                                    :0F-3A-three-byte))
            ;; Because of strict-opcode-p, we know that instructions without
            ;; the following CPUID features have empty opcode.vex and
            ;; opcode.evex fields, which means that they are non-AVX opcodes.
            (remove-insts-with-feat same-opcode-insts
                                    (append (list :avx :avx2 :bmi1 :bmi2)
                                            *avx512-feature-flags*))
          ;; Similarly, we know that instructions with these CPUID features are
          ;; AVX opcodes.
          (keep-insts-with-feat same-opcode-insts
                                (append (list :avx :avx2 :bmi1 :bmi2)
                                        *avx512-feature-flags*))))
       ((when (endp relevant-insts)) rest)
       (preCondNeeded? (< 1 (len relevant-insts)))
       ((mv moreCondNeeded? dispatch)
        (create-dispatch-for-one-opcode relevant-insts map-key wrld))
       (condNeeded? (or preCondNeeded? moreCondNeeded?)))
    (cons (cons
           ;; Case statements need to consider only the low 8-bits of the
           ;; opcode.
           (loghead 8 first-opcode)
           (if condNeeded?
               `((cond ,@dispatch))
             `(,dispatch)))
          rest)))

;; ----------------------------------------------------------------------
