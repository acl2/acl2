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
(include-book "std/strings/hexify" :dir :system)
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
    (b* ((rest (rest cell))
         (alt-opcodes (car rest))
         ((unless (alistp alt-opcodes))
          (er hard? 'get-string-name-of-simple-cell
              "~%Expected to be alist: ~p0~%"
              alt-opcodes))
         (opcode-names (strip-cars alt-opcodes))
         ((unless (string-listp opcode-names))
          (er hard? 'get-string-name-of-simple-cell
              "~%Expected to be string-listp: ~p0~%"
              opcode-names)))
      (str::fast-string-append-lst (insert-slash-in-list opcode-names))))

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

(define create-call-from-semantic-info ((info semantic-function-info-p)
                                        (world plist-worldp))
  :guard-hints (("Goal" :in-theory (e/d (semantic-function-info-p) ())))

  ;; (create-call-from-semantic-info
  ;;  '(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
  ;;           (operation . #.*OP-ADD*)))
  ;;  (w state))
  (if (equal info nil)
      (mv "Unimplemented"
          (replace-formals-with-arguments
           'x86-step-unimplemented
           '((message . "Opcode Unimplemented in x86isa!"))
           world))
    (b* ((rest (cdr info)))
      (if (equal (car rest) :no-instruction)
          (mv
           "Reserved"
           (replace-formals-with-arguments
            'x86-illegal-instruction
            '((message . "Reserved Opcode!"))
            world))
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
         (replace-formals-with-arguments
          (car rest) (cdr rest) world)))))
  ///

  (defthm stringp-of-mv-nth-0-create-call-from-semantic-info
    (stringp
     (mv-nth 0 (create-call-from-semantic-info info world))))

  (defthm true-listp-of-mv-nth-1-create-call-from-semantic-info
    (true-listp
     (mv-nth 1 (create-call-from-semantic-info info world)))))

(define create-dispatch-from-no-extensions-simple-cell
  ((cell simple-cell-p)
   (world plist-worldp))
  (b* (((when (member-equal (car cell) *group-numbers*))
        (mv ""
            (er hard? 'create-dispatch-from-no-extensions-simple-cell
                "~%We don't expect groups here: ~p0~%"
                cell)))
       (rest (cdr cell))
       (semantic-info (get-semantic-function-info-p rest)))
    (create-call-from-semantic-info semantic-info world))

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
            (create-call-from-semantic-info '(:fn . (:no-instruction)) world)))
        (mv ""
            `((t ,dispatch))))

    (b* ((opcode-descriptor (car desc-list))
         (opcode-identifier (car opcode-descriptor))
         ((unless (equal (cdr (assoc-equal :opcode opcode-identifier))
                         (+ escape-bytes opcode)))
          (create-case-dispatch-for-opcode-extensions-aux
           opcode (cdr desc-list) world :escape-bytes escape-bytes))
         (opcode-cell (cdr opcode-descriptor))
         (vex (cdr (assoc-equal :vex opcode-identifier)))
         (reg (cdr (assoc-equal :reg opcode-identifier)))
         (prefix (cdr (assoc-equal :prefix opcode-identifier)))
         (mod (cdr (assoc-equal :mod opcode-identifier)))
         (r/m (cdr (assoc-equal :r/m opcode-identifier)))
         (condition
          `(and
            ;; TODO: Check for VEX here.
            ,@(and reg
                   `((equal (mrm-reg modr/m) ,reg)))
            ,@(and mod
                   (if (equal mod :mem)
                       `((not (equal (mrm-mod modr/m) #b11)))
                     `((equal (mrm-mod modr/m) #b11))))
            ,@(and r/m
                   `((equal (mrm-r/m modr/m) ,r/m)))
            ,@(and prefix
                   `((equal mandatory-prefix ,prefix)))))
         ((mv doc-string dispatch)
          (create-dispatch-from-no-extensions-simple-cell
           opcode-cell world))
         (this-doc-string
          (if (or vex prefix reg mod r/m)
              (concatenate 'string
                           " <td> @('"
                           (str::pretty
                            `(,@(and vex    `((:VEX ,vex)))
                              ,@(and prefix `((:PFX ,prefix)))
                              ,@(and reg    `((:REG ,reg)))
                              ,@(and mod    `((:MOD ,mod)))
                              ,@(and r/m    `((:R/M ,r/m))))
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
                                     opcode-descriptor-p)
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
   (cell simple-cell-p)
   (world plist-worldp)
   &key
   ((escape-bytes natp) '0))

  ;; (create-dispatch-from-simple-cell
  ;;  0 (caar *one-byte-opcode-map-lst*) (w state))
  ;; (create-dispatch-from-simple-cell
  ;;  #x80 (car (nth 8 *one-byte-opcode-map-lst*)) (w state))

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
         ((or
           (and (basic-simple-cell-p cell)
                (or (stringp (car cell))
                    (member-equal (car cell)
                                  *simple-cells-standalone-legal-keywords*)))
           (equal (car cell) ':ALT))
          (b* (((mv doc-string dispatch)
                (create-dispatch-from-no-extensions-simple-cell cell world))
               (doc-string (concatenate 'string " <td> " doc-string " </td>")))
            (mv doc-string dispatch)))
         (t
          (mv "" '(nil)))))
       (string-name-of-simple-cell
        (get-string-name-of-simple-cell cell))
       (doc-string
        (concatenate 'string
                     " <td> " (or string-name-of-simple-cell "") " </td> "
                     doc-string)))
    (mv doc-string dispatch))


  ///

  (defthm stringp-mv-nth-0-create-dispatch-from-simple-cell
    (stringp
     (mv-nth 0
             (create-dispatch-from-simple-cell
              start-opcode cell world :escape-bytes escape-bytes)))))

(define create-dispatch-from-compound-cell
  ((start-opcode natp)
   (cell compound-cell-p)
   (world plist-worldp)
   &key
   ((escape-bytes natp) '0))

  :guard-hints (("Goal" :in-theory (e/d ()
                                        ((str::pretty-fn)
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
       (o64 (cdr (assoc-equal :o64 cell)))
       (i64 (cdr (assoc-equal :i64 cell)))
       (no-prefix (cdr (assoc-equal :no-prefix cell)))
       (66-prefix (cdr (assoc-equal :66 cell)))
       (F3-prefix (cdr (assoc-equal :F3 cell)))
       (F2-prefix (cdr (assoc-equal :F2 cell)))
       ((unless (and (or (not o64) (simple-cell-p o64))
                     (or (not i64) (simple-cell-p i64))
                     (or (not no-prefix) (simple-cell-p no-prefix))
                     (or (not 66-prefix) (simple-cell-p 66-prefix))
                     (or (not F3-prefix) (simple-cell-p F3-prefix))
                     (or (not F2-prefix) (simple-cell-p F2-prefix))))
        (mv "" '(nil)))
       ((mv o64-doc o64-dispatch)
        (if o64
            (create-dispatch-from-simple-cell
             start-opcode o64 world :escape-bytes escape-bytes)
          (mv "" '(nil))))
       ((mv i64-doc i64-dispatch)
        (if i64
            (create-dispatch-from-simple-cell
             start-opcode i64 world :escape-bytes escape-bytes)
          (mv "" '(nil))))
       ((mv 66-prefix-doc 66-prefix-dispatch)
        (if 66-prefix
            (create-dispatch-from-simple-cell
             start-opcode 66-prefix world :escape-bytes escape-bytes)
          (mv "" '(nil))))
       ((mv F2-prefix-doc F2-prefix-dispatch)
        (if F2-prefix
            (create-dispatch-from-simple-cell
             start-opcode F2-prefix world :escape-bytes escape-bytes)
          (mv "" '(nil))))
       ((mv F3-prefix-doc F3-prefix-dispatch)
        (if F3-prefix
            (create-dispatch-from-simple-cell
             start-opcode F3-prefix world :escape-bytes escape-bytes)
          (mv "" '(nil))))
       ((mv no-prefix-doc no-prefix-dispatch)
        (if no-prefix
            (create-dispatch-from-simple-cell
             start-opcode no-prefix world :escape-bytes escape-bytes)
          (mv "" '(nil))))
       (doc-string
        (str::fast-string-append-lst
         (if
             (and (not o64)
                  (not i64)
                  (not 66-prefix)
                  (not F2-prefix)
                  (not F3-prefix)
                  (not no-prefix))

             (list "<td> </td> <td> </td>")

           (list
            ;; Inserting empty second column, which usually holds the name
            ;; of the instruction or instruction group for simple cells:
            " <td> </td> <td> <table> "
            (if o64
                (concatenate
                 'string
                 " <tr> <td> @(':o64') </td> " o64-doc " </tr>")
              "")
            (if i64
                (concatenate
                 'string
                 " <tr> <td> @(':i64') </td> " i64-doc " </tr>")
              "")
            (if 66-prefix
                (concatenate
                 'string
                 " <tr> <td> @(':66') </td> " 66-prefix-doc " </tr>")
              "")
            (if F2-prefix
                (concatenate
                 'string
                 " <tr> <td> @(':F2') </td> " F2-prefix-doc " </tr>")
              "")
            (if F3-prefix
                (concatenate
                 'string
                 " <tr> <td> @(':F3') </td> " F3-prefix-doc " </tr>")
              "")
            (if no-prefix
                (concatenate
                 'string
                 " <tr> <td> @('No-Pfx') </td> " no-prefix-doc " </tr>")
              "")

            " </table> </td> "))))
       (dispatch
        `(,@(and o64
                 `(((64-bit-modep x86)
                    ,o64-dispatch)))
          ,@(and i64
                 `(((not (64-bit-modep x86))
                    ,i64-dispatch)))
          ,@(and 66-prefix
                 `(((equal mandatory-prefix #.*mandatory-66h*)
                    ,66-prefix-dispatch)))
          ,@(and F2-prefix
                 `(((equal mandatory-prefix #.*mandatory-F2h*)
                    ,F2-prefix-dispatch)))
          ,@(and F3-prefix
                 `(((equal mandatory-prefix #.*mandatory-F3h*)
                    ,F3-prefix-dispatch)))
          ,@(and no-prefix
                 `(((and
                     (not (equal mandatory-prefix #.*mandatory-66h*))
                     (not (equal mandatory-prefix #.*mandatory-F2h*))
                     (not (equal mandatory-prefix #.*mandatory-F3h*)))
                    ,no-prefix-dispatch)))
          (t
           ;; Catch-all case:
           ;; ,(create-call-from-semantic-info
           ;;   '(:fn . (:no-instruction)) world)
           (x86-illegal-instruction
            "Reserved or Illegal Opcode!" x86)))))
    (mv doc-string `(cond ,@dispatch)))

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
           "Reserved or Illegal Opcode!" x86))))
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