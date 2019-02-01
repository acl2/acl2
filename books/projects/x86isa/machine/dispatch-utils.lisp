; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; Copyright (C) 2018, Centaur Technology, Inc.
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
(include-book "std/strings/pretty" :dir :system)

;; Utilities to generate opcode dispatch functions from the annotated opcode
;; maps.

;; ----------------------------------------------------------------------

(defconst *x86isa-printconfig*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-lowercase t))

(define get-string-name-of-basic-simple-cell ((cell basic-simple-cell-p))
  :prepwork ((local (in-theory (e/d (basic-simple-cell-p) ()))))
  (if (mbt (basic-simple-cell-p cell))
      (string (first cell))
    "")

  ///

  (defthm stringp-of-get-string-name-of-basic-simple-cell
    (stringp (get-string-name-of-basic-simple-cell cell))))

(define insert-slash-in-list ((lst string-listp))
  (if (or (equal (len lst) 1)
          (endp lst))
      lst
    (cons (car lst)
          (cons "/" (insert-slash-in-list (cdr lst)))))

  ///

  (defthm string-listp-of-insert-slash-in-list
    (implies (string-listp lst)
             (string-listp (insert-slash-in-list lst)))))

(define get-string-name-of-simple-cell ((cell simple-cell-p))
  :guard-hints (("Goal" :do-not-induct t))
  :prepwork ((local (in-theory (e/d (simple-cell-p
                                     basic-simple-cell-p
                                     basic-simple-cells-p)
                                    ()))))
  (if (basic-simple-cell-p cell)
      (get-string-name-of-basic-simple-cell cell)
    (if (equal (car cell) ':EXT)
        (b* ((ext-opcode-desc-list (rest cell))
             ((unless (opcode-descriptor-list-p ext-opcode-desc-list))
              (er hard? 'get-string-name-of-simple-cell
                  "~%Expected to be opcode-descriptor-list-p: ~p0~%"
                  ext-opcode-desc-list))
             (desc-cells (strip-cdrs ext-opcode-desc-list))
             ((unless (alistp desc-cells))
              (er hard? 'get-string-name-of-simple-cell
                  "~%Expected to be alist: ~p0~%"
                  desc-cells))
             (opcode-names (strip-cars desc-cells))
             ((unless (string-listp opcode-names))
              (er hard? 'get-string-name-of-simple-cell
                  "~%Expected to be string-listp: ~p0~%"
                  opcode-names)))
          (str::fast-string-append-lst (insert-slash-in-list opcode-names)))
      (er hard? 'get-string-name-of-simple-cell
          "~%This should've been unreachable!~% Cell: ~p0~%"
          cell)))

  ///

  (defthm maybe-stringp-of-get-string-name-of-simple-cell
    (acl2::maybe-stringp (get-string-name-of-simple-cell cell))))

(define replace-element (x y lst)
  (if (atom lst)
      lst
    (if (equal (car lst) x)
        (cons y (replace-element x y (cdr lst)))
      (cons (car lst) (replace-element x y (cdr lst)))))
  ///
  (defthm true-listp-of-replace-element
    (implies (true-listp lst)
             (true-listp (replace-element x y lst)))))

(define replace-formals-with-arguments-aux ((bindings alistp)
                                            (formals true-listp))
  (if (endp bindings)
      formals
    (b* ((binding     (car bindings))
         (formal      (car binding))
         (argument    (cdr binding))
         (new-formals (replace-element formal argument formals)))
      (replace-formals-with-arguments-aux (cdr bindings) new-formals)))
  ///
  (defthm true-listp-of-replace-formals-with-arguments-aux
    (implies (true-listp formals)
             (true-listp (replace-formals-with-arguments-aux
                          bindings formals)))))

(define replace-formals-with-arguments ((fn symbolp)
                                        (bindings alistp)
                                        (world plist-worldp))

  (b* ((formals (acl2::formals fn world))
       ((unless (true-listp formals)) nil)
       (args    (replace-formals-with-arguments-aux bindings formals))
       (call    (cons fn args)))
    call)
  ///
  (defthm true-listp-of-replace-formals-with-arguments
    (true-listp (replace-formals-with-arguments fn bindings world))))

(define create-exceptions-check ((info exception-info-p))
  :guard-hints (("Goal" :in-theory (e/d (exception-info-p) ())))
  (if (atom info) nil
    (b* ((exception (caar info))
         (exception-list (cdar info)))
      (if (eq exception :ex)
          `(let ((chk-ex (or ,@exception-list)))
             (or chk-ex
                 ,(create-exceptions-check (cdr info))))
      `(if (or ,@exception-list) (quote ,exception)
         ,(create-exceptions-check (cdr info)))))))

(local (defthm exception-info-is-alist
         (implies (exception-info-p x) (alistp x))
         :hints (("Goal" :in-theory (enable exception-info-p)))))

(define make-exception-handling-cases ((exception-info exception-info-p)
                                       unimplemented illegal
                                       (world plist-worldp))
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

(define create-call-from-semantic-info ((info semantic-function-info-p)
                                        (exception-info exception-info-p)
                                        (world plist-worldp))
  :guard-hints (("Goal" :in-theory (e/d (semantic-function-info-p) ())))

  ;; (create-call-from-semantic-info
  ;;  '(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
  ;;           (operation . #.*OP-ADD*)))
  ;;     '(:ud  . ((ud-Lock-used)
  ;;               (equal
  ;;                (cpuid-flag
  ;;                 #ux_01
  ;;                 :reg #.*ecx*
  ;;                 :bit 23)
  ;;                0)))
  ;;  (w state))

  (b* ((exception-check  (create-exceptions-check exception-info))
       (unimplemented    (replace-formals-with-arguments
                          'x86-step-unimplemented
                          '((message . "Opcode Unimplemented in x86isa!"))
                          world))
       (illegal          (replace-formals-with-arguments
                          'x86-illegal-instruction
                          '((message . "#UD Encountered!"))
                          world))
       (exception-cases  (make-exception-handling-cases exception-info
                                                        unimplemented
                                                        illegal
                                                        world)))

    (if (equal info nil)
        (mv "Unimplemented"
            (if exception-info
                `(let ((fault-var ,exception-check))
                   (if fault-var (case fault-var ,@exception-cases)
                     ,unimplemented))
              unimplemented))

      (b* ((rest (cdr info)))
        (if (equal (car rest) :no-instruction)
            (mv "Reserved" illegal)
          (mv
           (concatenate
            'string
            "@(tsee "
            (str::pretty (car rest) :config *x86isa-printconfig*)
            ")"
            (if (cdr rest)
                (concatenate
                 'string " -- <br/> "
                 (str::pretty (cdr rest) :config *x86isa-printconfig*))
              ""))
           (if exception-info
               `(let ((fault-var ,exception-check))
                  (if fault-var
                      (case fault-var ,@exception-cases)
                    ,(replace-formals-with-arguments
                      (car rest) (cdr rest) world)))
             (replace-formals-with-arguments
              (car rest) (cdr rest) world)))))))

  ///

  (defthm stringp-of-mv-nth-0-create-call-from-semantic-info
    (stringp
     (mv-nth 0 (create-call-from-semantic-info info exception-info world))))

  (defthm true-listp-of-mv-nth-1-create-call-from-semantic-info
    (true-listp
     (mv-nth 1 (create-call-from-semantic-info info exception-info world)))))


(define create-dispatch-from-no-extensions-simple-cell
  ((cell simple-cell-p)
   (world plist-worldp))
  (b* (((when (member-equal (car cell) *group-numbers*))
        (mv ""
            (er hard? 'create-dispatch-from-no-extensions-simple-cell
                "~%We don't expect groups here: ~p0~%"
                cell)))
       (rest (cdr cell))
       (exception-info (get-exception-info rest))
       (semantic-info (get-semantic-function-info rest)))
    (create-call-from-semantic-info semantic-info exception-info world))

  ///

  (defthm stringp-of-mv-nth-1-create-dispatch-from-no-extensions-simple-cell
    (stringp
     (mv-nth 0 (create-dispatch-from-no-extensions-simple-cell cell world))))

  (defthm true-listp-of-mv-nth-1-create-dispatch-from-no-extensions-simple-cell
    (true-listp
     (mv-nth 1 (create-dispatch-from-no-extensions-simple-cell cell world)))))

(define create-case-dispatch-for-opcode-extensions-aux
  ((opcode natp)
   (desc-list opcode-descriptor-list-p)
   (world plist-worldp)
   &key
   ((escape-bytes natp) '0))

  :verify-guards nil
  :guard-hints (("Goal"
                 :in-theory (e/d (opcode-descriptor-list-p
                                  opcode-descriptor-p)
                                 ())
                 :do-not-induct t))

  (if (endp desc-list)

      (b* (((mv & dispatch)
            ;; This is a catch-all case --- so we ignore the doc here.
            (create-call-from-semantic-info
             '(:fn . (:no-instruction))
             nil ;; No Exceptions
             world)))
        (mv ""
            `((t ,dispatch))))

    (b* ((opcode-descriptor (car desc-list))
         (opcode-identifier (car opcode-descriptor))
         ((unless (equal (cdr (assoc-equal :opcode opcode-identifier))
                         (+ escape-bytes opcode)))
          (create-case-dispatch-for-opcode-extensions-aux
           opcode (cdr desc-list) world :escape-bytes escape-bytes))
         (opcode-cell (cdr opcode-descriptor))
         ;; (vex         (cdr (assoc-equal :vex opcode-identifier)))
         ;; (evex        (cdr (assoc-equal :evex opcode-identifier)))
         (feat        (cdr (assoc-equal :feat opcode-identifier)))
         (mode        (cdr (assoc-equal :mode opcode-identifier)))
         (reg         (cdr (assoc-equal :reg opcode-identifier)))
         (prefix      (cdr (assoc-equal :prefix opcode-identifier)))
         (prefix-val  (case prefix
                        (:66 #x66)
                        (:F3 #xF3)
                        (:F2 #xF2)
                        (t ;; :no-prefix
                         #x0)))
         (mod         (cdr (assoc-equal :mod opcode-identifier)))
         (r/m         (cdr (assoc-equal :r/m opcode-identifier)))
         (rex         (cdr (assoc-equal :rex opcode-identifier)))
         (condition
          `(and
            ;; ,@(if evex
            ;;       `((not (equal evex-prefixes 0)))
            ;;     `((equal evex-prefixes 0)))
            ;; ,@(if vex
            ;;       `((not (equal vex-prefixes 0)))
            ;;     `((equal vex-prefixes 0)))
            ,@(and mode
                   (if (equal mode :o64)
                       `((equal proc-mode #.*64-bit-mode*))
                     `((not (equal proc-mode #.*64-bit-mode*)))))
            ,@(and feat
                   `((equal (feature-flags-macro ',feat) 1)))
            ,@(and reg
                   `((equal (modr/m->reg modr/m) ,reg)))
            ,@(and mod
                   (if (equal mod :mem)
                       `((not (equal (modr/m->mod modr/m) #b11)))
                     `((equal (modr/m->mod modr/m) #b11))))
            ,@(and r/m
                   `((equal (modr/m->r/m modr/m) ,r/m)))
            ,@(and prefix
                   `((equal mandatory-prefix ,prefix-val)))
            ,@(and rex
                   ;; TODO: :w and :not-w are the only two REX-based conditions
                   ;; right now.  See opcode-maps for details.
                   (if (equal rex :w)
                       `((logbitp #.*w* rex-byte))
                     `((not (logbitp #.*w* rex-byte)))))))
         ((mv doc-string dispatch)
          (create-dispatch-from-no-extensions-simple-cell
           opcode-cell world))
         (this-doc-string
          (if (or ;; evex vex
               prefix reg mod r/m)
              (concatenate 'string
                           " <td> @('"
                           (str::pretty
                            `( ;; ,@(and evex   `((:EVEX ,evex)))
                              ;; ,@(and vex    `((:VEX  ,vex)))
                              ,@(and feat   `((:FEAT ,feat)))
                              ,@(and mode   `((:MODE ,mode)))
                              ,@(and prefix `((:PFX  ,prefix)))
                              ,@(and reg    `((:REG  ,reg)))
                              ,@(and mod    `((:MOD  ,mod)))
                              ,@(and r/m    `((:R/M  ,r/m)))
                              ,@(and rex    `((:REX  ,rex))))
                            :config *x86isa-printconfig*)
                           ;; (str::pretty (cdr condition) ;; remove the 'and
                           ;;              :config *x86isa-printconfig*)
                           "') </td> <td> "
                           doc-string
                           " </td> ")
            (concatenate 'string
                         " <td> "
                         doc-string
                         " </td> ")))
         (string-name-of-simple-cell
          (get-string-name-of-simple-cell opcode-cell))
         (this-doc-string
          (if string-name-of-simple-cell
              (concatenate
               'string
               " <tr> <td> "
               string-name-of-simple-cell
               " </td> "
               this-doc-string
               " </tr> ")
            this-doc-string))
         (cell-dispatch
          `(,condition ,dispatch))

         ((mv final-doc-string cells-dispatch)
          (create-case-dispatch-for-opcode-extensions-aux
           opcode (cdr desc-list) world :escape-bytes escape-bytes)))
      (mv (concatenate 'string this-doc-string final-doc-string)
          (cons cell-dispatch cells-dispatch))))

  ///

  (defthm stringp-of-mv-nth-0-create-case-dispatch-for-opcode-extensions-aux
    (stringp
     (mv-nth 0
             (create-case-dispatch-for-opcode-extensions-aux
              opcode desc-list world :escape-bytes escape-bytes))))

  (verify-guards create-case-dispatch-for-opcode-extensions-aux-fn
    :hints (("Goal" :in-theory (e/d (opcode-descriptor-list-p
                                     opcode-descriptor-p
                                     simple-cell-p)
                                    ())))))

(define create-case-dispatch-for-opcode-extensions
  ((opcode natp)
   (desc-list opcode-descriptor-list-p)
   (world plist-worldp)
   &key
   ((escape-bytes natp) '0))

  (b* (((mv doc-string dispatch)
        (create-case-dispatch-for-opcode-extensions-aux
         opcode desc-list world :escape-bytes escape-bytes))
       (doc-string (concatenate 'string
                                " <td> <table> "
                                doc-string
                                " </table> </td> ")))
    (mv doc-string `(cond ,@dispatch)))

  ///

  (defthm stringp-of-mv-nth-0-create-case-dispatch-for-opcode-extensions
    (stringp
     (mv-nth 0
             (create-case-dispatch-for-opcode-extensions
              opcode desc-list world :escape-bytes escape-bytes)))))

(define create-dispatch-from-simple-cell
  ((start-opcode natp)
   (cell)
   (world plist-worldp)
   &key
   ((escape-bytes natp) '0))

  ;; (create-dispatch-from-simple-cell
  ;;  0 (caar *one-byte-opcode-map-lst*) (w state))
  ;; (create-dispatch-from-simple-cell
  ;;  #x80 (car (nth 8 *one-byte-opcode-map-lst*)) (w state))

  (cond ((or (not cell)
             (not (simple-cell-p cell)))
         (mv "ILLEGAL SIMPLE CELL. ERROR!" '(nil)))

        (t
         (b* (((mv doc-string dispatch)
               (cond
                ((and (basic-simple-cell-p cell)
                      (member-equal (car cell) *group-numbers*))
                 (b* (((mv doc-string dispatch)
                       (create-case-dispatch-for-opcode-extensions
                        start-opcode
                        (cdr (assoc-equal
                              (car cell)
                              *opcode-extensions-by-group-number*))
                        world
                        :escape-bytes escape-bytes)))
                   (mv doc-string dispatch)))
                ((and (equal (car cell) ':EXT)
                      (opcode-descriptor-list-p (cdr cell)))
                 (b* (((mv doc-string dispatch)
                       (create-case-dispatch-for-opcode-extensions
                        start-opcode
                        (cdr cell)
                        world
                        :escape-bytes escape-bytes)))
                   (mv doc-string dispatch)))
                ((and (basic-simple-cell-p cell)
                      (or (stringp (car cell))
                          (member-equal (car cell)
                                        *simple-cells-standalone-legal-keywords*)))
                 (b* (((mv doc-string dispatch)
                       (create-dispatch-from-no-extensions-simple-cell cell world))
                      (doc-string (concatenate 'string " <td> " doc-string " </td>")))
                   (mv doc-string dispatch)))
                (t
                 (mv "UNREACHABLE!" '(nil)))))
              (string-name-of-simple-cell
               (get-string-name-of-simple-cell cell))
              (doc-string
               (concatenate 'string
                            " <td> " (or string-name-of-simple-cell "") " </td> "
                            doc-string)))
           (mv doc-string dispatch))))


  ///

  (defthm stringp-mv-nth-0-create-dispatch-from-simple-cell
    (stringp
     (mv-nth 0
             (create-dispatch-from-simple-cell
              start-opcode cell world :escape-bytes escape-bytes)))))

(define create-compound-cell-subdoc-aux (cell name doc)
  (if cell
      (let ((name (acl2::str-fix name))
            (doc  (acl2::str-fix doc)))
        (concatenate 'string " <tr> <td> @('" name "') </td> " doc " </tr>"))
    "")

  ///

  (defthm stringp-of-create-compound-cell-subdoc-aux
    (stringp (create-compound-cell-subdoc-aux cell name doc))))

(define create-compound-cell-subdoc
  (o64 o64-doc
   i64 i64-doc
   no-prefix no-prefix-doc
   66-prefix 66-prefix-doc
   F2-prefix F2-prefix-doc
   F3-prefix F3-prefix-doc
   ;; v-prefix v-prefix-doc
   ;; v66-prefix v66-prefix-doc
   ;; vF2-prefix vF2-prefix-doc
   ;; vF3-prefix vF3-prefix-doc
   ;; ev-prefix ev-prefix-doc
   ;; ev66-prefix ev66-prefix-doc
   ;; evF2-prefix evF2-prefix-doc
   ;; evF3-prefix evF3-prefix-doc
   )

  :returns (str stringp)

  (str::fast-string-append-lst
   (if
       (and (not o64)
            (not i64)
            (not 66-prefix)
            (not F2-prefix)
            (not F3-prefix)
            (not no-prefix)
            ;; (not v66-prefix)
            ;; (not vF2-prefix)
            ;; (not vF3-prefix)
            ;; (not v-prefix)
            ;; (not ev66-prefix)
            ;; (not evF2-prefix)
            ;; (not evF3-prefix)
            ;; (not ev-prefix)
            )

       (list "<td> </td> <td> </td>")

     (list
      ;; Inserting empty second column, which usually holds the name
      ;; of the instruction or instruction group for simple cells:
      " <td> </td> <td> <table> "

      (create-compound-cell-subdoc-aux o64          ":o64"       o64-doc)
      (create-compound-cell-subdoc-aux i64          ":i64"       i64-doc)
      (create-compound-cell-subdoc-aux 66-prefix    ":66"        66-prefix-doc)
      (create-compound-cell-subdoc-aux F2-prefix    ":F2"        F2-prefix-doc)
      (create-compound-cell-subdoc-aux F3-prefix    ":F3"        F3-prefix-doc)
      (create-compound-cell-subdoc-aux no-prefix    ":No-Pfx"    no-prefix-doc)
      ;; (create-compound-cell-subdoc-aux v-prefix     ":v-No-Pfx"  v-prefix-doc)
      ;; (create-compound-cell-subdoc-aux v66-prefix   ":v66"       v66-prefix-doc)
      ;; (create-compound-cell-subdoc-aux vF2-prefix   ":vF2"       vF2-prefix-doc)
      ;; (create-compound-cell-subdoc-aux vF3-prefix   ":vF3"       vF3-prefix-doc)
      ;; (create-compound-cell-subdoc-aux ev-prefix    ":ev-No-Pfx" ev-prefix-doc)
      ;; (create-compound-cell-subdoc-aux ev66-prefix  ":ev66"      ev66-prefix-doc)
      ;; (create-compound-cell-subdoc-aux evF2-prefix  ":evF2"      evF2-prefix-doc)
      ;; (create-compound-cell-subdoc-aux evF3-prefix  ":evF3"      evF3-prefix-doc)

      " </table> </td> "))))

(define create-compound-cell-subdispatch
  (o64 o64-dispatch
       i64 i64-dispatch
       no-prefix no-prefix-dispatch
       66-prefix 66-prefix-dispatch
       F2-prefix F2-prefix-dispatch
       F3-prefix F3-prefix-dispatch
       ;; v-prefix v-prefix-dispatch
       ;; v66-prefix v66-prefix-dispatch
       ;; vF2-prefix vF2-prefix-dispatch
       ;; vF3-prefix vF3-prefix-dispatch
       ;; ev-prefix ev-prefix-dispatch
       ;; ev66-prefix ev66-prefix-dispatch
       ;; evF2-prefix evF2-prefix-dispatch
       ;; evF3-prefix evF3-prefix-dispatch
       )

  `(cond
    ,@(and o64
           `(((equal proc-mode #.*64-bit-mode*)
              ,o64-dispatch)))
    ,@(and i64
           `(((not (equal proc-mode #.*64-bit-mode*))
              ,i64-dispatch)))
    ,@(and no-prefix
           `(((equal mandatory-prefix 0)
              ;; (and
              ;;  (equal vex-prefixes 0)
              ;;  (equal evex-prefixes 0)
              ;;  (equal mandatory-prefix 0))
              ,no-prefix-dispatch)))
    ,@(and 66-prefix
           `(((equal mandatory-prefix #.*mandatory-66h*)
              ;; (and (equal vex-prefixes 0)
              ;;      (equal evex-prefixes 0)
              ;;      (equal mandatory-prefix #.*mandatory-66h*))
              ,66-prefix-dispatch)))
    ,@(and F2-prefix
           `(((equal mandatory-prefix #.*mandatory-F2h*)
              ;; (and (equal vex-prefixes 0)
              ;;      (equal evex-prefixes 0)
              ;;      (equal mandatory-prefix #.*mandatory-F2h*))
              ,F2-prefix-dispatch)))
    ,@(and F3-prefix
           `(((equal mandatory-prefix #.*mandatory-F3h*)
              ;; (and (equal vex-prefixes 0)
              ;;      (equal evex-prefixes 0)
              ;;      (equal mandatory-prefix #.*mandatory-F3h*))
              ,F3-prefix-dispatch)))
    ;; ,@(and v-prefix
    ;;        `(((and
    ;;            (not (equal vex-prefixes 0))
    ;;            (equal mandatory-prefix 0))
    ;;           ,v-prefix-dispatch)))
    ;; ,@(and v66-prefix
    ;;        `(((and
    ;;            (not (equal vex-prefixes 0))
    ;;            (equal mandatory-prefix #.*mandatory-66h*))
    ;;           ,v66-prefix-dispatch)))
    ;; ,@(and vF3-prefix
    ;;        `(((and
    ;;            (not (equal vex-prefixes 0))
    ;;            (equal mandatory-prefix #.*mandatory-F3h*))
    ;;           ,vF3-prefix-dispatch)))
    ;; ,@(and vF2-prefix
    ;;        `(((and
    ;;            (not (equal vex-prefixes 0))
    ;;            (equal mandatory-prefix #.*mandatory-F2h*))
    ;;           ,vF2-prefix-dispatch)))
    ;; ,@(and ev-prefix
    ;;        `(((and
    ;;            (not (equal evex-prefixes 0))
    ;;            (equal mandatory-prefix 0))
    ;;           ,ev-prefix-dispatch)))
    ;; ,@(and ev66-prefix
    ;;        `(((and
    ;;            (not (equal evex-prefixes 0))
    ;;            (equal mandatory-prefix #.*mandatory-66h*))
    ;;           ,ev66-prefix-dispatch)))
    ;; ,@(and evF3-prefix
    ;;        `(((and
    ;;            (not (equal evex-prefixes 0))
    ;;            (equal mandatory-prefix #.*mandatory-F3h*))
    ;;           ,evF3-prefix-dispatch)))
    ;; ,@(and evF2-prefix
    ;;        `(((and
    ;;            (not (equal evex-prefixes 0))
    ;;            (equal mandatory-prefix #.*mandatory-F2h*))
    ;;           ,evF2-prefix-dispatch)))
    (t
     ;; Catch-all case:
     ;; ,(create-call-from-semantic-info
     ;;   '(:fn . (:no-instruction)) world)
     (x86-illegal-instruction
      "Reserved or Illegal Opcode!" start-rip temp-rip x86))))

(define create-dispatch-from-compound-cell ((start-opcode natp)
                                            (cell compound-cell-p)
                                            (world plist-worldp)
                                            &key
                                            ((escape-bytes natp) '0))

  :guard-hints (("Goal" :in-theory (e/d ()
                                        (natp
                                         not
                                         (str::pretty-fn)
                                         string-append
                                         str::fast-string-append-lst
                                         (tau-system)))))

  ;; (create-dispatch-from-compound-cell
  ;;  #x10
  ;;  (nth 0 (nth 1 *two-byte-opcode-map-lst*))
  ;;  (w state))

  (b* ((keys (strip-cars cell))
       ((unless (subsetp-equal keys *compound-cells-legal-keys*))
        (cw "~%cell: ~p0~%" cell)
        (mv "" '(nil)))
       (o64         (cdr (assoc-equal :o64 cell)))
       (i64         (cdr (assoc-equal :i64 cell)))
       (no-prefix   (cdr (assoc-equal :no-prefix cell)))
       (66-prefix   (cdr (assoc-equal :66 cell)))
       (F3-prefix   (cdr (assoc-equal :F3 cell)))
       (F2-prefix   (cdr (assoc-equal :F2 cell)))
       ;; (v-prefix    (cdr (assoc-equal :v cell)))
       ;; (v66-prefix  (cdr (assoc-equal :v66 cell)))
       ;; (vF3-prefix  (cdr (assoc-equal :vF3 cell)))
       ;; (vF2-prefix  (cdr (assoc-equal :vF2 cell)))
       ;; (ev-prefix   (cdr (assoc-equal :ev cell)))
       ;; (ev66-prefix (cdr (assoc-equal :ev66 cell)))
       ;; (evF3-prefix (cdr (assoc-equal :evF3 cell)))
       ;; (evF2-prefix (cdr (assoc-equal :evF2 cell)))

       ((mv o64-doc o64-dispatch)
        (create-dispatch-from-simple-cell
         start-opcode o64 world :escape-bytes escape-bytes))
       ((mv i64-doc i64-dispatch)
        (create-dispatch-from-simple-cell
         start-opcode i64 world :escape-bytes escape-bytes))
       ((mv 66-prefix-doc 66-prefix-dispatch)
        (create-dispatch-from-simple-cell
         start-opcode 66-prefix world :escape-bytes escape-bytes))
       ((mv F2-prefix-doc F2-prefix-dispatch)
        (create-dispatch-from-simple-cell
         start-opcode F2-prefix world :escape-bytes escape-bytes))
       ((mv F3-prefix-doc F3-prefix-dispatch)
        (create-dispatch-from-simple-cell
         start-opcode F3-prefix world :escape-bytes escape-bytes))
       ((mv no-prefix-doc no-prefix-dispatch)
        (create-dispatch-from-simple-cell
         start-opcode no-prefix world :escape-bytes escape-bytes))
       ;; ((mv v66-prefix-doc v66-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode v66-prefix world :escape-bytes escape-bytes))
       ;; ((mv vF2-prefix-doc vF2-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode vF2-prefix world :escape-bytes escape-bytes))
       ;; ((mv vF3-prefix-doc vF3-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode vF3-prefix world :escape-bytes escape-bytes))
       ;; ((mv v-prefix-doc v-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode v-prefix world :escape-bytes escape-bytes))
       ;; ((mv ev66-prefix-doc ev66-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode ev66-prefix world :escape-bytes escape-bytes))
       ;; ((mv evF2-prefix-doc evF2-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode evF2-prefix world :escape-bytes escape-bytes))
       ;; ((mv evF3-prefix-doc evF3-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode evF3-prefix world :escape-bytes escape-bytes))
       ;; ((mv ev-prefix-doc ev-prefix-dispatch)
       ;;  (create-dispatch-from-simple-cell
       ;;   start-opcode ev-prefix world :escape-bytes escape-bytes))

       (doc-string
        (create-compound-cell-subdoc
         o64 o64-doc
         i64 i64-doc
         no-prefix no-prefix-doc
         66-prefix 66-prefix-doc
         F2-prefix F2-prefix-doc
         F3-prefix F3-prefix-doc
         ;; v-prefix v-prefix-doc
         ;; v66-prefix v66-prefix-doc
         ;; vF2-prefix vF2-prefix-doc
         ;; vF3-prefix vF3-prefix-doc
         ;; ev-prefix ev-prefix-doc
         ;; ev66-prefix ev66-prefix-doc
         ;; evF2-prefix evF2-prefix-doc
         ;; evF3-prefix evF3-prefix-doc
         ))

       (dispatch
        (create-compound-cell-subdispatch
         o64 o64-dispatch
         i64 i64-dispatch
         no-prefix no-prefix-dispatch
         66-prefix 66-prefix-dispatch
         F2-prefix F2-prefix-dispatch
         F3-prefix F3-prefix-dispatch
         ;; v-prefix v-prefix-dispatch
         ;; v66-prefix v66-prefix-dispatch
         ;; vF2-prefix vF2-prefix-dispatch
         ;; vF3-prefix vF3-prefix-dispatch
         ;; ev-prefix ev-prefix-dispatch
         ;; ev66-prefix ev66-prefix-dispatch
         ;; evF2-prefix evF2-prefix-dispatch
         ;; evF3-prefix evF3-prefix-dispatch
         )))

    (mv doc-string dispatch))

  ///

  (defthm stringp-mv-nth-0-create-dispatch-from-compound-cell
    (stringp
     (mv-nth 0
             (create-dispatch-from-compound-cell
              start-opcode cell world :escape-bytes escape-bytes)))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (e/d ()
                             ((str::pretty-fn)
                              str::fast-string-append-lst
                              string-append))))))

(define create-dispatch-from-opcode-cell
  ((start-opcode natp)
   (cell opcode-cell-p)
   (world plist-worldp)
   &key
   ((escape-bytes natp) '0))

  (b* (((mv doc-string cell-dispatch)
        (if (simple-cell-p cell)
            (create-dispatch-from-simple-cell
             start-opcode cell world :escape-bytes escape-bytes)
          (if (compound-cell-p cell)
              (create-dispatch-from-compound-cell
               start-opcode cell world :escape-bytes escape-bytes)
            (mv "" '(nil)))))
       (doc-string
        (concatenate 'string
                     " <tr> <td> "
                     (str::hexify start-opcode)
                     " </td> " doc-string " </tr> "))
       (dispatch
        (cons start-opcode (list cell-dispatch))))
    (mv doc-string dispatch))

  ///

  (defthm stringp-mv-nth-0-create-dispatch-from-opcode-cell
    (stringp
     (mv-nth 0
             (create-dispatch-from-opcode-cell
              start-opcode cell world :escape-bytes escape-bytes)))))

(define create-dispatch-from-opcode-row ((start-opcode natp)
                                         (row opcode-row-p)
                                         (world plist-worldp)
                                         &key
                                         ((escape-bytes natp) '0))
  :measure (len row)

  (if (endp row)
      (mv "" nil)
    (b* ((cell (car row))
         ((mv doc-string cell-dispatch)
          (create-dispatch-from-opcode-cell
           start-opcode cell world :escape-bytes escape-bytes))
         ((when (equal cell-dispatch '(nil)))
          (mv
           ""
           (er hard? 'create-dispatch-from-opcode-row
               "~%Something went wrong for this cell: ~p0~%"
               cell)))
         ((mv rest-doc-string rest-cell-dispatch)
          (create-dispatch-from-opcode-row
           (1+ start-opcode) (cdr row) world :escape-bytes escape-bytes)))
      (mv
       (concatenate 'string doc-string rest-doc-string)
       (cons cell-dispatch rest-cell-dispatch))))

  ///

  (defthm stringp-of-mv-nth-0-create-dispatch-from-opcode-row
    (stringp
     (mv-nth 0
             (create-dispatch-from-opcode-row
              start-opcode row world :escape-bytes escape-bytes))))

  (defthm true-listp-of-mv-nth-1-create-dispatch-from-opcode-row
    (true-listp
     (mv-nth 1
             (create-dispatch-from-opcode-row
              start-opcode row world :escape-bytes escape-bytes)))))

(define create-dispatch-from-opcode-map-aux ((start-opcode natp)
                                             (map opcode-map-p)
                                             (world plist-worldp)
                                             &key
                                             ((escape-bytes natp) '0))
  :verify-guards nil

  (if (endp map)
      (mv
       ""
       `((t
          ;; Catch-all case:
          ;; ,(create-call-from-semantic-info
          ;;   '(:fn . (:no-instruction)) world)
          (x86-illegal-instruction
           "Reserved or Illegal Opcode!" start-rip temp-rip x86))))
    (b* ((row (car map))
         ((mv row-doc-string row-dispatch)
          (create-dispatch-from-opcode-row
           start-opcode row world :escape-bytes escape-bytes))
         ((mv rest-doc-string rest-dispatch)
          (create-dispatch-from-opcode-map-aux
           (+ 16 start-opcode) (cdr map) world :escape-bytes escape-bytes)))
      (mv (concatenate 'string row-doc-string rest-doc-string)
          (append row-dispatch rest-dispatch))))
  ///

  (defthm stringp-of-mv-nth-0-create-dispatch-from-opcode-map-aux
    (stringp
     (mv-nth 0
             (create-dispatch-from-opcode-map-aux
              start-opcode row world :escape-bytes escape-bytes))))

  (defthm true-listp-of-mv-nth-1-create-dispatch-from-opcode-map-aux
    (true-listp
     (mv-nth 1 (create-dispatch-from-opcode-map-aux
                start-opcode map world :escape-bytes escape-bytes))))

  (verify-guards create-dispatch-from-opcode-map-aux-fn
    :hints (("Goal" :in-theory (e/d (opcode-map-p) ())))))

(define create-dispatch-from-opcode-map ((map opcode-map-p)
                                         (world plist-worldp)
                                         &key
                                         ((escape-bytes natp) '0))

  (b* (((mv doc-string dispatch)
        (create-dispatch-from-opcode-map-aux
         0 map world :escape-bytes escape-bytes)))

    (mv (concatenate 'string "<table> " doc-string " </table>")
        dispatch))

  ///

  (defthm stringp-of-mv-nth-0-create-dispatch-from-opcode-map
    (stringp
     (mv-nth 0
             (create-dispatch-from-opcode-map
              row world :escape-bytes escape-bytes))))

  (defthm true-listp-of-mv-nth-1-create-dispatch-from-opcode-map
    (true-listp
     (mv-nth 1 (create-dispatch-from-opcode-map
                map world :escape-bytes escape-bytes)))))

;; ----------------------------------------------------------------------

;; VEX- and EVEX-encoded instructions:

(define vex-keyword-case-gen ((prefix-case (kwd-or-key-consp prefix-case t)))

  (if (atom prefix-case)
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
         `()))
    (case (car prefix-case)
      (:REG   `((equal (modr/m->reg modr/m) ,(cdr prefix-case))))
      (:MOD    (if (equal (cdr prefix-case) :mem)
                   `((not (equal (modr/m->mod modr/m) #b11)))
                 `((equal (modr/m->mod modr/m) #b11))))
      (otherwise
       ;; Should be unreachable.
       `()))))

(define evex-keyword-case-gen ((prefix-case (kwd-or-key-consp prefix-case nil)))

  (if (atom prefix-case)
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
         `()))
    (case (car prefix-case)
      (:REG   `((equal (modr/m->reg modr/m) ,(cdr prefix-case))))
      (:MOD    (if (equal (cdr prefix-case) :mem)
                   `((not (equal (modr/m->mod modr/m) #b11)))
                 `((equal (modr/m->mod modr/m) #b11))))
      (otherwise
       ;; Should be unreachable.
       `()))))

(define avx-keyword-case-gen ((prefix-case (kwd-or-key-consp prefix-case vex?))
                              (vex? booleanp))
  (if vex?
      (vex-keyword-case-gen prefix-case)
    (evex-keyword-case-gen prefix-case)))

(define avx-opcode-case-gen-aux
  ((case-info (avx-cases-okp case-info vex?))
   (vex? booleanp))
  (if (endp case-info)
      nil
    `(,@(avx-keyword-case-gen (car case-info) vex?)
      ,@(avx-opcode-case-gen-aux (cdr case-info) vex?))))

(define member-equal! (e x)
  (and (consp x)
       (or (equal e (first x))
           (member-equal! e (rest x)))))

(define subset-equal! (x y)
  (or (atom x)
      (and (member-equal! (first x) y)
           (subset-equal! (rest x) y))))

(define find-avx-exc-type (kwds (cell avx-exc-type-cell-p) top)
  (cond ((endp cell)
         (er hard? 'find-avx-exc-type
             "one of the types should have matched!:~x0" (list kwds top)))
        ((subset-equal! (caar cell) kwds)
         (cadar cell))
        (t (find-avx-exc-type kwds (cdr cell) top))))

(define feat-look ((kwds true-listp)
                   (opcode-desc true-listp))
  :returns (cpuid-flags symbol-listp :hyp :guard)
  (if (atom opcode-desc)
      opcode-desc
    (b* ((info (car opcode-desc)))
      (if (and (consp info)
               (eql (car info) :FEAT))
          (if (symbol-listp (cdr info))
              (cdr info)
            nil)
        (feat-look kwds (cdr opcode-desc))))))

(define avx-opcode-case-gen ((opcode-variant
                              (and (consp opcode-variant)
                                   (avx-cases-okp (car opcode-variant) vex?)
                                   (avx-opcode-desc-okp (cdr opcode-variant))))
                             (vex? booleanp)
                             (cell avx-exc-type-cell-p)
                             state)
  (b* (((unless (consp opcode-variant))
        (er hard? 'avx-opcode-case-gen
            "internal error: ill-formed opcode-variant:~p0" opcode-variant))
       (kwd-lst (car opcode-variant))
       (opcode-desc (cdr opcode-variant))
       (pref (cond ((member-eq :66 kwd-lst) :66)
                   ((member-eq :F2 kwd-lst) :F2)
                   ((member-eq :F3 kwd-lst) :F3)
                   (t :no-prefix)))
       (feature-flags (feat-look kwd-lst (car opcode-desc)))
       (unimplemented (replace-formals-with-arguments
                       'x86-step-unimplemented
                       '((message . "Opcode Unimplemented in x86isa!"))
                       (w state)))
       (illegal       (replace-formals-with-arguments
                       'x86-illegal-instruction
                       '((message . "#UD Encountered!"))
                       (w state)))
       (kwd-lst (if (or (member-eq :NDS kwd-lst)
                        (member-eq :NDD kwd-lst)
                        (member-eq :DDS kwd-lst))
                    kwd-lst
                  (cons :UNUSED-VVVV kwd-lst)))
       (kwd-lst (if (eq pref :no-prefix)
                    (cons :no-prefix kwd-lst)
                  kwd-lst))
       (exc-type (find-avx-exc-type kwd-lst cell cell))
       (exception-check (if vex?
                            `(chk-exc-vex ,exc-type ,feature-flags)
                          `(chk-exc-evex ,exc-type ,feature-flags)))
       (exception-cases (make-exception-handling-cases '((:ex . nil))
                                                       unimplemented
                                                       illegal
                                                       (w state))))
    `((and ,@(avx-opcode-case-gen-aux kwd-lst vex?))
      (let ((fault-var ,exception-check))
        (if fault-var (case fault-var ,@exception-cases)
          ,unimplemented)))))

(local
 (defthm avx-opcode-cases-okp-implies-true-listp-fwd
   (implies (avx-opcode-cases-okp variants vex?)
            (true-listp variants))
   :hints (("Goal" :in-theory (e/d (avx-opcode-cases-okp) ())))
   :rule-classes :forward-chaining))

(define avx-opcode-cases-gen ((opcode-variants true-listp)
                              (vex? booleanp)
                              (cell avx-exc-type-cell-p)
                              state)
  :guard (avx-opcode-cases-okp opcode-variants vex?)
  (if (endp opcode-variants)
      `((t
         ,(replace-formals-with-arguments
           'x86-illegal-instruction
           '((message . "Reserved or Illegal Opcode!"))
           (w state))))
    (b* ((opcode-variant (car opcode-variants))
         ((unless (and (consp opcode-variant)
                       (avx-cases-okp (car opcode-variant) vex?)
                       (avx-opcode-desc-okp (cdr opcode-variant))))
          `())
         (first-case (avx-opcode-case-gen opcode-variant vex? cell state)))
      `(,first-case
         ,@(avx-opcode-cases-gen (cdr opcode-variants) vex? cell state)))))

(define avx-case-gen ((map (avx-maps-well-formed-p map vex?))
                      (exc-types avx-exc-type-map-p)
                      (vex? booleanp)
                      state)
  :guard (equal (len map) (len exc-types))
  :guard-hints (("Goal" :in-theory (e/d (avx-maps-well-formed-p
                                         avx-opcode-cases-okp)
                                        ())))
  (if (endp map)
      `((t
         ,(replace-formals-with-arguments
           'x86-illegal-instruction
           '((message . "Reserved or Illegal Opcode!"))
           (w state))))
    (b* ((first (car map))
         (opcode (car first))
         (opcode-variants (cdr first))
         (type-cell (cadar exc-types))
         ((unless (avx-opcode-cases-okp opcode-variants vex?))
          (er hard? 'avx-case-gen
              "internal error: ill-formed opcode-variants:~x0" opcode-variants)))
      `((,opcode (cond ,@(avx-opcode-cases-gen
                          opcode-variants vex? type-cell state)))
        ,@(avx-case-gen (cdr map) (cdr exc-types) vex? state)))))

;; (avx-case-gen *vex-0F-opcodes*
;;               *vex-0F-exc-types*
;;               t state)

;; ----------------------------------------------------------------------

;; To collapse vex- and evex-encoded instructions with the same opcode and
;; mnemonic but different VEX fields, we can do something like
;; intersect-vex-keywords below.  This'll likely be a good thing to do when we
;; have instruction semantic functions for these instructions.

;; (define intersect-vex-keywords ((k1 acl2::keyword-listp)
;;                              (k2 acl2::keyword-listp))
;;   ;; inputs: kwd-lists corresponding to a vex-encoded instruction with the same
;;   ;; opcode and the same mnemonic
;;   (b* ((common (intersection$ k1 k2))
;;        (k1-unique (set-difference$ k1 k2))
;;        (k2-unique (set-difference$ k2 k1))
;;        (vvvv-clash
;;      ;; TODO: Deal with instructions where vvvv is always used.
;;      (or (and (member :UNUSED-VVVV k1-unique)
;;               (or (member :NDS k2-unique)
;;                   (member :NDD k2-unique)
;;                   (member :DDS k2-unique)))
;;          (and (member :UNUSED-VVVV k2-unique)
;;               (or (member :NDS k1-unique)
;;                   (member :NDD k1-unique)
;;                   (member :DDS k1-unique)))))
;;        (l-clash
;;      (or (and (or (member :LIG  k1-unique)
;;                   (member :128  k1-unique)
;;                   (member :L0   k1-unique)
;;                   (member :LZ   k1-unique))
;;               (or (member :256  k2-unique)
;;                   (member :L1   k2-unique)))
;;          (and (or (member :LIG  k2-unique)
;;                   (member :128  k2-unique)
;;                   (member :L0   k2-unique)
;;                   (member :LZ   k2-unique))
;;               (or (member :256  k1-unique)
;;                   (member :L1   k1-unique)))))
;;        (pp-clash
;;      ;; I don't think pp-clash will ever come into play, but eh, who knows
;;      ;; with all these crazy encodings...
;;      )
;;        (w-clash
;;      (or (and (or (member :WIG  k1-unique)
;;                   (member :W0   k1-unique))
;;               (member :W1   k2-unique))
;;          (and (or (member :WIG  k2-unique)
;;                   (member :W0   k2-unique))
;;               (member :W1   k1-unique)))))
;;     ...))

;; ----------------------------------------------------------------------
