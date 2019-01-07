; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; Copyright (C) 2019, Centaur Technology, Inc.
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
; Shilpi Goel         <shilpi@centtech.com>

(in-package "X86ISA")

(include-book "opcode-maps")
(include-book "opcode-map-structs")

(define remove-all ((x true-listp)
                    (y true-listp))
  :short "Remove all elements in @('x') from @('y')"
  :enabled t
  (if (endp x)
      y
    (remove-all (cdr x) (remove-equal (car x) y))))

(define convert-opcode-extensions ((opcode natp)
                                   (desc-list opcode-descriptor-list-p)
                                   (insert-into-opcode true-listp))
  :mode :program
  :verify-guards nil
  (b* (((when (endp desc-list)) nil)
       (desc (car desc-list))
       (opcode-identifier (car desc))
       ((unless (equal (cdr (assoc-equal :opcode opcode-identifier)) opcode))
        (convert-opcode-extensions opcode (cdr desc-list) insert-into-opcode))
       ;; *opcode-descriptor-legal-keys*
       (reg (cdr (assoc-equal :reg opcode-identifier)))
       (mod (cdr (assoc-equal :mod opcode-identifier)))
       (r/m (cdr (assoc-equal :r/m opcode-identifier)))
       (prefix (cdr (assoc-equal :prefix opcode-identifier)))
       ;; (vex (cdr (assoc-equal :vex opcode-identifier)))
       (mode (cdr (assoc-equal :mode opcode-identifier)))
       (feat (cdr (assoc-equal :feat opcode-identifier)))
       (rex (cdr (assoc-equal :rex opcode-identifier)))
       (cell (cdr desc))
       (mnemonic (car cell))
       ((unless (stringp mnemonic))
        (- (cw "~% ~p0: Ignoring non-string mnemonic: ~p1 ~%"
               __function__ mnemonic))
        ;; Ignore :none --- why pad the opcode maps unnecessarily?
        (convert-opcode-extensions opcode (cdr desc-list) insert-into-opcode))
       (semantic-info (get-semantic-function-info (cdr cell)))
       (exception-info (get-exception-info (cdr cell)))
       (num-ops (nth 1 cell))
       (arg
        (case num-ops
          (0 nil)
          (1 `(arg :op1 ',(nth 2 cell)))
          (2 `(arg :op1 ',(nth 2 cell) :op2 ',(nth 3 cell)))
          (3 `(arg :op1 ',(nth 2 cell) :op2 ',(nth 3 cell)
                   :op3 ',(nth 4 cell)))
          (t `(arg :op1 ',(nth 2 cell) :op2 ',(nth 3 cell)
                   :op3 ',(nth 4 cell) :op4 ',(nth 5 cell)))))
       (new-rest (remove-exception-info cell))
       (new-rest (remove-semantic-function-info new-rest))
       (superscripts (nthcdr (+ 2 ;; For mnemonic and num-ops
                                num-ops)
                             new-rest))
       (others
        `(,@(and reg `(:reg ,reg))
          ,@(and mod `(:mod ,mod))
          ,@(and r/m `(:r/m ,r/m))
          ,@(and prefix `(:pfx ,prefix))
          ;; ,@(and vex `(:vex ,vex))
          ,@(and mode `(:mode ,mode))
          ,@(and feat `(:feat ',feat))
          ,@(and rex `(:rex ,rex))
          ,@(and  superscripts `(:superscripts ',superscripts))
          ,@insert-into-opcode))
       (fn (if (consp semantic-info)
               (cdr semantic-info)
             nil)))
    (cons
     `(inst
       ,mnemonic
       (op :op ,opcode ,@others)
       ,arg
       ',fn
       ',exception-info)
     (convert-opcode-extensions opcode (cdr desc-list) insert-into-opcode))))

(define convert-basic-simple-cell ((opcode natp)
                                   (cell basic-simple-cell-p)
                                   (insert-into-opcode true-listp))
  :mode :program
  :verify-guards nil
  (b* ((first (car cell))
       (rest (cdr cell))
       (exception-info (get-exception-info cell))
       (semantic-info (get-semantic-function-info cell))
       (new-rest (remove-exception-info cell))
       (new-rest (remove-semantic-function-info new-rest))
       ;; (- (cw "~% new-rest: ~p0 ~%" new-rest))
       )
    (if (stringp first)
        (b* ((num-ops (nth 1 cell))
             (superscripts (nthcdr (+ 2 ;; For mnemonic and num-ops
                                      num-ops)
                                   new-rest))
             (arg
              (case num-ops
                (0 nil)
                (1 `(arg :op1 ',(nth 2 cell)))
                (2 `(arg :op1 ',(nth 2 cell) :op2 ',(nth 3 cell)))
                (3 `(arg :op1 ',(nth 2 cell) :op2 ',(nth 3 cell)
                         :op3 ',(nth 4 cell)))
                (t `(arg :op1 ',(nth 2 cell) :op2 ',(nth 3 cell)
                         :op3 ',(nth 4 cell) :op4 ',(nth 5 cell)))))
             (fn (if (consp semantic-info)
                     (cdr semantic-info)
                   nil))
             (op (if insert-into-opcode
                     `(op :op ,opcode ,@insert-into-opcode
                          ,@(and superscripts `(:superscripts ',superscripts)))
                   `(op :op ,opcode
                        ,@(and superscripts `(:superscripts ',superscripts))))))
          (list
           `(inst
             ,first ;; mnemonic
             ,op
             ,arg
             ',fn
             ',exception-info)))
      (if (equal first :NONE)
          (cw "~% ~p0: Ignoring non-string mnemonic: ~p1 ~%"
              __function__ first)
        (if (member-equal first
                          (remove-all
                           '(:NONE ;; Ignoring :NONE
                             :GROUP-1 :GROUP-1A
                             :GROUP-2 :GROUP-3
                             :GROUP-4 :GROUP-5
                             :GROUP-6 :GROUP-7
                             :GROUP-8 :GROUP-9
                             :GROUP-10 :GROUP-11
                             :GROUP-12 :GROUP-13
                             :GROUP-14 :GROUP-15
                             :GROUP-16 :GROUP-17)
                           *simple-cells-legal-keywords*))
            (b* ((superscripts (nthcdr 1 ;; For group ID
                                       new-rest))
                 (op (if insert-into-opcode
                         `(op :op ,opcode ,@insert-into-opcode
                              ,@(and superscripts `(:superscripts ',superscripts)))
                       `(op :op ,opcode
                            ,@(and superscripts `(:superscripts ',superscripts))))))
              (list
               `(inst ,first ,op
                      'nil
                      ',(if (consp semantic-info)
                            (cdr semantic-info)
                          nil)
                      ',(get-exception-info rest))))
          ;; Opcode Extensions
          (convert-opcode-extensions
           opcode
           (cdr (assoc-equal first *opcode-extensions-by-group-number*))
           insert-into-opcode))))))

#||

(convert-basic-simple-cell
 #x0
 '("ADD" 2 (E b)  (G b)
   (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
           (operation . #.*OP-ADD*)))
   (:ud . ((ud-Lock-used-Dest-not-Memory-Op))))
 nil)

The :1a in :Group-xxx cells is ignored. These superscripts are taken from
cells in *opcode-extensions-by-group-number* instead.

(convert-basic-simple-cell #x80 '(:Group-1 :1a) nil)
||#

(define convert-simple-cell ((opcode natp)
                             (cell simple-cell-p)
                             (insert-into-opcode true-listp))
  :mode :program
  :verify-guards nil
  (if (basic-simple-cell-p cell)
      (convert-basic-simple-cell opcode cell insert-into-opcode)
    ;; With :EXT:
    (convert-opcode-extensions opcode (cdr cell) insert-into-opcode)))

#||
(convert-simple-cell #ux0F_12 '(:EXT
                                (((:opcode . #ux0F_12)
                                  (:mod    . :mem)) .
                                  ("MOVLPS"    3 (V q)  (H q)  (M q)
                                   (:fn . (x86-movlps/movlpd-Op/En-RM))
                                   (:ex . ((chk-exc :type-5 (:sse))))))
                                (((:opcode . #ux0F_12)
                                  (:mod    . #b11)) .
                                  ("MOVHLPS"    3 (V q)  (H q)  (U q)
                                   (:ex . ((chk-exc :type-7 (:sse)))))))
                     nil)
||#

(define convert-compound-cell ((opcode natp)
                               (cell compound-cell-p))
  :mode :program
  :verify-guards nil
  (if (endp cell)
      nil
    (b* ((pair (car cell))
         (key (car pair))
         (simple-cell (cdr pair))
         (basic-cell? (basic-simple-cell-p cell))
         ((when (or (eql key :i64)
                    (eql key :o64)))
          (append (convert-simple-cell opcode simple-cell
                                       (if basic-cell? `(:mode ,key) nil))
                  (convert-compound-cell opcode (cdr cell))))
         ((when
              ;; op-pfx-p
              (member-equal key '(:NO-PREFIX :66 :F3 :F2
                                             ;; :v :v66 :vF3 :vF2 ;; vex separated out.
                                             ;; :ev :ev66 :evF3 :evF2 ;; evex separated out.
                                             )))
          (append (convert-simple-cell opcode simple-cell
                                       (if basic-cell? `(:pfx ,key) nil))
                  (convert-compound-cell opcode (cdr cell)))))
      (convert-compound-cell opcode (cdr cell)))))

#||
(convert-compound-cell #ux06
                       '((:i64 . ("PUSH ES" 0
                                  (:fn . (x86-push-segment-register))
                                  (:ud  . ((ud-Lock-used)))))
                         (:o64 . ("#UD" 0
                                  (:ud  . (t))
                                  (:fn . (x86-illegal-instruction
                                          (message .
                                                   "PUSH ES is illegal in the 64-bit mode!")))))))

(convert-compound-cell #ux82
                       '((:i64 . (:Group-1 :1a))
                         (:o64 . ("#UD" 0
                                  (:ud  . (t))
                                  (:fn .
                                       (x86-illegal-instruction
                                        (message .
                                                 "Opcode 0x82 is illegal in the 64-bit mode!")))))))

(convert-compound-cell #ux0F_77
                       '((:no-prefix . ("EMMS"        0
                                        (:ud . ((ud-Lock-used)
                                                (equal (cr0Bits->em (cr0)) 1)))))
                         (:v         . ("VZEROUPPER/VZEROALL"  0
                                        (:ex . ((chk-exc :type-8 (:avx))))))))
||#

;; (define convert-cell ((opcode natp)
;;                       (cell opcode-cell-p))
;;   :mode :program
;;   (if (compound-cell-p cell)
;;       (convert-compound-cell opcode cell)
;;     (convert-simple-cell opcode cell nil)))

(define get-cpuid-flag-info (opcode-desc)
  :mode :program
  (if (atom opcode-desc)
      opcode-desc
    (if (and (consp (car opcode-desc))
             (eql (caar opcode-desc) :FEAT))
        (car opcode-desc)
      (get-cpuid-flag-info (cdr opcode-desc)))))

(define get-reg-from-avx ((lst true-listp))
  (if (endp lst)
      nil
    (if (and (consp (car lst))
             (equal (caar lst) :REG))
        (cdar lst)
      (get-reg-from-avx (cdr lst)))))

(define get-mod-from-avx ((lst true-listp))
  (if (endp lst)
      nil
    (if (and (consp (car lst))
             (equal (caar lst) :MOD))
        (cdar lst)
      (get-mod-from-avx (cdr lst)))))

(define remove-reg/mod-from-avx ((lst true-listp))
  (if (endp lst)
      nil
    (if (and (consp (car lst))
             (or (equal (caar lst) :REG)
                 (equal (caar lst) :MOD)))
        (remove-reg/mod-from-avx (cdr lst))
      (cons (car lst) (remove-reg/mod-from-avx (cdr lst))))))


(define convert-avx-opcode (opcode
                            (avx-opcode true-listp))
  :mode :program
  :guard (equal (len avx-opcode) 2)

  (if (atom avx-opcode)
      nil
    (b* ((cases (car avx-opcode))
         (desc (cadr avx-opcode))
         (new-opcode-desc (remove-cpuid-flag-info desc))
         ;; (- (cw "~% cases: ~p0 desc: ~p1 new-opcode-desc: ~p2~%"
         ;;        cases desc new-opcode-desc))
         (feat (get-cpuid-flag-info desc))
         (feat (if feat (cdr feat) nil))
         (feat (if feat `(:feat ',feat) nil))
         (reg (get-reg-from-avx cases))
         (mod (get-mod-from-avx cases))
         (reg/mod (if reg
                      `(:reg ,reg)
                    nil))
         (reg/mod (if mod
                      (append `(:mod ,mod) reg/mod)
                    reg/mod))
         (- (cw "~% reg/mod: ~p0~%" reg/mod))
         (avx-pre (remove-reg/mod-from-avx cases))
         (avx-pre (remove-equal :vex (remove-equal :evex avx-pre)))
         (avx (if (member-equal :vex cases)
                  `(:vex ',avx-pre)
                `(:evex ',avx-pre)))
         (mnemonic (car desc))
         (arg (if (< 1 (len new-opcode-desc))
                  (b* ((num-ops (second new-opcode-desc))
                       (arg
                        (case num-ops
                          (0 nil)
                          (1 `(arg :op1 ',(nth 2 new-opcode-desc)))
                          (2 `(arg :op1 ',(nth 2 new-opcode-desc)
                                   :op2 ',(nth 3 new-opcode-desc)))
                          (3 `(arg :op1 ',(nth 2 new-opcode-desc)
                                   :op2 ',(nth 3 new-opcode-desc)
                                   :op3 ',(nth 4 new-opcode-desc)))
                          (t `(arg :op1 ',(nth 2 new-opcode-desc)
                                   :op2 ',(nth 3 new-opcode-desc)
                                   :op3 ',(nth 4 new-opcode-desc)
                                   :op4 ',(nth 5 new-opcode-desc))))))
                    arg)
                nil)))
      `(inst
        ,mnemonic
        (op :op ,opcode ,@avx ,@feat ,@reg/mod)
        ,arg
        nil nil ;; fn and exception info --- not implemented yet
        ))))

(define convert-avx-opcodes (opcode
                             (avx-opcodes true-list-listp))
  :mode :program
  (if (endp avx-opcodes)
      nil
    (cons (convert-avx-opcode opcode (car avx-opcodes))
          (convert-avx-opcodes opcode (cdr avx-opcodes)))))

(define convert-cell ((opcode natp)
                      (cell opcode-cell-p))
  :mode :program
  (b* ((vex? (cond ((8bits-p opcode) nil)
                   ((16bits-p opcode)
                    (assoc (loghead 8 opcode) *vex-0F-opcodes*))
                   ((and (24bits-p opcode)
                         (equal (logtail 8 opcode) #ux0F_38))
                    (assoc (loghead 8 opcode) *vex-0F38-opcodes*))
                   ((and (24bits-p opcode)
                         (equal (logtail 8 opcode) #ux0F_3A))
                    (assoc (loghead 8 opcode) *vex-0F3A-opcodes*))
                   (t nil)))
       (evex? (cond ((8bits-p opcode) nil)
                    ((16bits-p opcode)
                     (assoc (loghead 8 opcode) *evex-0F-opcodes*))
                    ((and (24bits-p opcode)
                          (equal (logtail 8 opcode) #ux0F_38))
                     (assoc (loghead 8 opcode) *evex-0F38-opcodes*))
                    ((and (24bits-p opcode)
                          (equal (logtail 8 opcode) #ux0F_3A))
                     (assoc (loghead 8 opcode) *evex-0F3A-opcodes*))
                    (t nil)))
       (vex-opcodes (if vex?
                        (convert-avx-opcodes opcode (cdr vex?))
                      nil))
       (evex-opcodes (if evex?
                         (convert-avx-opcodes opcode (cdr evex?))
                       nil)))
    (append
     (if (compound-cell-p cell)
         (convert-compound-cell opcode cell)
       (convert-simple-cell opcode cell nil))
     vex-opcodes
     evex-opcodes)))

(define convert-row (opcode row)
  :mode :program
  (if (endp row)
      nil
    (append (convert-cell opcode (car row))
            (convert-row (1+ opcode) (cdr row)))))

(define convert-map (opcode map)
  :mode :program
  (if (endp map)
      nil
    (append (convert-row opcode (car map))
            (convert-map (+ 16 opcode) (cdr map)))))

(define eval-pre-map (x state)
  :mode :program
  (if (atom x)
      (mv nil x state)
    (b* (((mv ?erp val state)
          (acl2::trans-eval
           (car x)
           'eval-pre-map state t))
         ;; (car val) is stobjs-out.
         ;; (- (cw "~%~p0~%" (inst-p (cdr val))))
         ((mv erp rest state)
          (eval-pre-map (cdr x) state))
         (all (cons (cdr val) rest))
         (erp (or erp (if (inst-list-p all) nil t))))
      (mv erp all state))))

;; ----------------------------------------------------------------------

;; (acl2::set-print-base-radix 16 state)

;; The following deal with vex and evex maps, in addition to the opcode
;; extensions map.  All of that stuff is hard-coded.
(make-event
 `(progn
    (defconst *pre-one-byte-opcode-map*
      ',(convert-map       #ux00 *one-byte-opcode-map-lst*))
    (defconst *pre-two-byte-opcode-map*
      ',(convert-map    #ux0F_00 *two-byte-opcode-map-lst*))
    (defconst *pre-0F-38-three-byte-opcode-map*
      ',(convert-map #ux0F_38_00 *0F-38-three-byte-opcode-map-lst*))
    (defconst *pre-0F-3A-three-byte-opcode-map*
      ',(convert-map #ux0F_3A_00 *0F-3A-three-byte-opcode-map-lst*))))

(make-event
 (mv-let (one-byte-opcode-map
          two-byte-opcode-map
          0F-38-three-byte-opcode-map
          0F-3A-three-byte-opcode-map
          state)
   (b* (((mv ?erp one-byte-map state)
         (eval-pre-map *pre-one-byte-opcode-map* state))
        ((mv ?erp two-byte-map state)
         (eval-pre-map *pre-two-byte-opcode-map* state))
        ((mv ?erp 0F-38-three-byte-map state)
         (eval-pre-map *pre-0F-38-three-byte-opcode-map* state))
        ((mv ?erp 0F-3A-three-byte-map state)
         (eval-pre-map *pre-0F-3A-three-byte-opcode-map* state)))
     (mv one-byte-map two-byte-map
         0F-38-three-byte-map 0F-3A-three-byte-map
         state))
   (mv nil
       `(progn
          (defconst *one-byte-opcode-map*         ',one-byte-opcode-map)
          (defconst *two-byte-opcode-map*         ',two-byte-opcode-map)
          (defconst *0F-38-three-byte-opcode-map* ',0F-38-three-byte-opcode-map)
          (defconst *0F-3A-three-byte-opcode-map* ',0F-3A-three-byte-opcode-map))
       state)))

(defthm inst-list-p-of-maps
  (and (inst-list-p *one-byte-opcode-map*)
       (inst-list-p *two-byte-opcode-map*)
       (inst-list-p *0F-38-three-byte-opcode-map*)
       (inst-list-p *0F-3A-three-byte-opcode-map*)))

;; ----------------------------------------------------------------------
