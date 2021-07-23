
;;!!! The next step is to write smt-to-acl2-expr.  Pretty much I just need to
;;!!! look at the supported functions in SMT-lib and translate them one-by-one.
;;!!! Also remember that this function has to return the size of the resulting
;;!!! bit vector.  I haven't fixed its call yet to reflect that.

;; This file contains the tranlator from the
;; Bit bector benchmarks to ACL2.

(in-package "ACL2")

(include-book "../sat/sulfa-dir-const")
(include-book "../clause-processors/sym-str")
(include-book "bv-lib" :skip-proofs-okp t :ttags (sat sat-cl))

(program)
(set-state-ok t)

(defun make-var-entry (var sz expr)
  (list* var sz expr))

(defun ve-var (var-entry)
  (car var-entry))

(defun ve-sz (var-entry)
  (cadr var-entry))

(defun ve-expr (var-entry)
  (cddr var-entry))

(defun print-bv-object (obj channel state)
  ;; Faster:
  (print-object$-fn obj nil channel state))
  ;; Prettier:
;;(fms! "~x0~%" (list (cons #\0 obj)) channel state nil))

(defun read-smt-file (filename state)
  (mv-let
   (channel state)
   (open-input-channel filename :object state)
   (mv-let
    (eof obj state)
    (read-object channel state)
    (if eof
        (mv (er hard 'read-smt-file
                "No objects in file: ~x0~%" filename)
            state)
      (let ((state (close-input-channel channel state)))
        (mv obj state))))))

(defun gen-names (str arg-types n acc)
  (cond
   ((endp arg-types)
    (revappend acc nil))
   (t
    (gen-names str
               (cdr arg-types)
               (1+ n)
               (cons (symbol-from-str-num str n)
                     acc)))))

(defun bv-type-size (type)
  (cond
   ((equal type 'bool)
    0)
   ((and (consp type) (equal (car type) 'bitvec))
    (cadr type))
   (t
    (er hard 'bv-type-size "Unrecognized type: ~x0~%" type))))

(defun gen-eq-expr (x y type)
  (cond
   ((equal type 'bool)
    `(iff ,x ,y))
   (t
    `(bv-eq-raw ,(bv-type-size type) ,x ,y))))

(defun gen-bv-eq-expr-list (str0 str1 arg-types n acc)
  (cond
   ((endp arg-types)
    acc)
   (t
    (let ((arg0 (symbol-from-str-num str0 n))
          (arg1 (symbol-from-str-num str1 n)))
      (gen-bv-eq-expr-list
       str0 str1 (cdr arg-types)
       (1+ n)
       (cons (gen-eq-expr arg0 arg1 (car arg-types))
             acc))))))

(defun output-defstub (sig channel state)
  (let* ((name (car sig))
         (raw-name (symbol-from-sym-str name "-RAW"))
         (rev-sig (revappend (cdr sig) nil))
         (ret-type (car rev-sig))
         (arg-types (revappend (cdr rev-sig) nil))
         (arg-names (gen-names "I" arg-types 0 nil))
         (axiom-name (symbol-from-sym-str raw-name "-AXIOM"))
         (obj `(encapsulate
                ((,raw-name ,arg-names t))
                (local (defun ,raw-name ,arg-names
                         (declare (ignore . ,arg-names))
                         t))
                (defthm ,axiom-name
                  (implies (and . ,(gen-bv-eq-expr-list "I" "J" arg-types 0 nil))
                           ,(gen-eq-expr
                             `(,raw-name . ,(gen-names "I" arg-types 0 nil))
                             `(,raw-name . ,(gen-names "J" arg-types 0 nil))
                             ret-type)))
                (in-theory (disable ,axiom-name))))
         (state (print-bv-object obj channel state))
         (obj `(defbv ,name ,arg-names
                 (sig . ,(cdr sig))
                 ,raw-name))
         (state (print-bv-object obj channel state))
         (obj `(in-theory (disable (:executable-counterpart ,name))))
         (state (print-bv-object obj channel state)))
    (mv (cons name arg-names) state)))

(defun output-defstubs (extrafuns acc channel state)
  (cond
   ((endp extrafuns)
    (mv acc state))
   (t
    (mv-let
     (sig state)
     (output-defstub (car extrafuns) channel state)
     (output-defstubs (cdr extrafuns) (cons sig acc) channel state)))))

(defun output-sig-events (sigs channel state)
  (let* ((sigs (revappend sigs *bv-defeval-sigs*))
         (obj `(def-b-if-meta ,sigs))
         (state (print-bv-object obj channel state))
         (obj `(deftheory raw-bv-theory
                 (union-theories (current-theory :here)
                                 (quote ,(strip-cars sigs)))))
         (state (print-bv-object obj channel state)))
    state))

(defun chars-to-num1 (char-list ans)
  (cond
   ((endp char-list)
    ans)
   (t
    (chars-to-num1 (cdr char-list)
                   (+ (digit-char-p (car char-list))
                      (* 10 ans))))))

(defun chars-to-num (char-list)
  (chars-to-num1 char-list 0))

(defun digit-char-listp (x)
  (cond
   ((endp x)
    t)
   ((digit-char-p (car x))
    (digit-char-listp (cdr x)))
   (t
    nil)))

(defun smt-bv-constp (expr)
  (and (symbolp expr)
       (< 0 (nfix (string< "bv" (string expr))))
       (digit-char-listp (cddr (coerce (string expr) 'list)))))

(mutual-recursion
(defun smt-to-acl2-expr-list (expr-list extra-fn-list var-alist acc-sizes acc)
  (cond
   ((endp expr-list)
    (mv (revappend acc-sizes nil)
        (revappend acc nil)))
   (t
    (mv-let
     (bv-sz bv-expr)
     (smt-to-acl2-expr (car expr-list) extra-fn-list var-alist)
     (smt-to-acl2-expr-list (cdr expr-list)
                            extra-fn-list var-alist
                            (cons bv-sz acc-sizes)
                            (cons bv-expr acc))))))

;; Convert an expression from the SMT benchmarks into ACL2
;; with our BV book.  Also returns the size of the resulting
;; bit vector as the first bit vector.

;; I got the list of bit-vector operations from:
;; http://combination.cs.uiowa.edu/smtlib/

;; Note that I've decided to handle equality and logical
;; operatives by converting them into bit-vector operations.
;;
;; The advantage, and disadvantage, of this is that it
;; keeps ACL2 from handling them specially (e.g. case-spliting
;; on if conditions).  They can always be simplified into
;; the logical operators if that's what we want.

;; The one exception to all this is let.  Since let isn't
;; really an operation, but rather more of a language
;; construct, I've decided to use ACL2's let.  If the explosion
;; get's out of hand, I'll have to find some way to contain it---
;; e.g. using bv-eq instead.

(defun smt-to-acl2-expr (expr extra-fn-list var-alist)
  (cond
   ((atom expr)
    (cond
     ((integerp expr)
      (mv 0 expr))
     ((eq expr '|true|)
      (mv 0 t))
     ((eq expr '|false|)
      (mv 0 nil))
     ((eq expr '|bit0|)
      (mv 1 '(bv-const 1 0)))
     ((eq expr '|bit1|)
      (mv 1 '(bv-const 1 1)))
     ((smt-bv-constp expr)
      ;; This is a 32-bit constant
      (let* ((num-chars (cddr (coerce (string expr) 'list)))
             (num (chars-to-num num-chars)))
        (mv 32 `(bv-const 32 ,num))))

     (t
      (let* ((var-entry (assoc-equal expr var-alist)))
        (cond
         (var-entry
          (mv (ve-sz var-entry) (ve-expr var-entry)))
         (t
          (mv 0
              (er hard 'smt-to-acl2-expr
                  "Unsupported expression: ~x0~%" expr))))))))

   ;; SMT let expressions have the format
   ;; (let (var var-expr) body)
   ((or (eq (car expr) '|let|)
        (eq (car expr) '|flet|))
    (let ((var (car (cadr expr)))
          (var-expr (cadr (cadr expr)))
          (body (caddr expr)))
      (mv-let
       (var-sz var-aexpr)
       (smt-to-acl2-expr var-expr extra-fn-list var-alist)
       (let ((var-alist (cons (make-var-entry var var-sz var)
                              var-alist)))
         (mv-let
          (body-sz body-aexpr)
          (smt-to-acl2-expr body extra-fn-list var-alist)
          (mv body-sz `(let ((,var ,var-aexpr)) ,body-aexpr)))))))

   (t
    (mv-let
     (arg-sizes args)
     (smt-to-acl2-expr-list (cdr expr) extra-fn-list var-alist nil nil)
     (cond
      ;; Bit vector extraction and concatenation
      ((and (consp (car expr)) (eq (caar expr) '|extract|))
       (mv (1+ (- (cadr (car expr)) (caddr (car expr))))
           `(bv-ex ,(car arg-sizes)
                   ,(cadr (car expr))
                   ,(caddr (car expr))
                   .
                   ,args)))
      ((and (consp (car expr)) (eq (caar expr) '|fill|))
       (mv (cadr (car expr))
           `(bv-repeat ,(car arg-sizes) ,(car args) ,(cadr (car expr)))))
      ((consp (car expr))
       (mv 0
           (er hard 'smt-to-acl2-expr
               "Unsupported expression: ~x0~%" expr)))
      ((eq (car expr) '|concat|)
       (mv (+ (car arg-sizes) (cadr arg-sizes))
           `(bv-concat ,(car arg-sizes) ,(cadr arg-sizes) . ,args)))

      ;; Bit vector operations
      ((eq (car expr) '|bvnot|)
       (mv (car arg-sizes)
           `(bv-not ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvand|)
       (mv (car arg-sizes)
           `(bv-and ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvor|)
       (mv (car arg-sizes)
           `(bv-or ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvxor|)
       (mv (car arg-sizes)
           `(bv-xor ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvadd|)
       (mv (car arg-sizes)
           `(bv-add ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvneg|)
       (mv (car arg-sizes)
           `(bv-neg ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvsub|)
       (mv (car arg-sizes)
           `(bv-sub ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvmul|)
       (mv (car arg-sizes)
           `(bv-mul ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvnand|)
       (mv (car arg-sizes)
           `(bv-nand ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvnor|)
       (mv (car arg-sizes)
           `(bv-nor ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|shift_left0|)
       (mv (car arg-sizes)
           `(shift-left0 ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|shift_left1|)
       (mv (car arg-sizes)
           `(shift-left1 ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|shift_right0|)
       (mv (car arg-sizes)
           `(shift-right0 ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|shift_right1|)
       (mv (car arg-sizes)
           `(shift-right1 ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|repeat|)
       (mv (* (cadr args) (car arg-sizes))
           `(bv-repeat ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|sign_extend|)
       (mv (+ (cadr args) (car arg-sizes))
           `(sign-extend ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|rotate_left|)
       (mv (car arg-sizes)
           `(bv-rotate-left ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|rotate_right|)
       (mv (car arg-sizes)
           `(bv-rotate-right ,(car arg-sizes) . ,args)))


      ;; Bit Vector predicates
      ((eq (car expr) '|bvleq|)
       (mv 0 `(bv-leq ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvlt|)
       (mv 0 `(bv-lt ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvgeq|)
       (mv 0 `(bv-geq ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvgt|)
       (mv 0 `(bv-gt ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvslt|)
       (mv 0 `(bv-s-lt ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvsleq|)
       (mv 0 `(bv-s-leq ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvsgt|)
       (mv 0 `(bv-s-gt ,(car arg-sizes) . ,args)))
      ((eq (car expr) '|bvsgeq|)
       (mv 0 `(bv-s-geq ,(car arg-sizes) . ,args)))


      ;; Equality
      ((eq (car expr) '|=|)
       (mv 0 `(bv-eq . ,args)))

      ;; if-then-else
      ((eq (car expr) '|ite|)
       (cond
        ((equal 0 (cadr arg-sizes))
         (mv 0 `(b-if . ,args)))
        (t
         (mv (cadr arg-sizes)
             `(bv-if ,(cadr arg-sizes) . ,args)))))

      ;; Logical connectives
      ((eq (car expr) '|not|)
       (mv 0 `(b-not . ,args)))
      ((eq (car expr) '|implies|)
       (mv 0 `(b-implies ,(car args) ,(cadr args))))
      ((eq (car expr) '|if_then_else|)
       (mv (cadr arg-sizes) `(b-if . ,args)))
      ((eq (car expr) '|and|)
       (mv 0 `(b-and . ,args)))
      ((eq (car expr) '|or|)
       (mv 0 `(b-or . ,args)))
      ((eq (car expr) '|xor|)
       (mv 0 `(b-xor . ,args)))
      ((eq (car expr) '|iff|)
       (mv 0 `(b-iff . ,args)))

      (t
       (let ((fn-entry (assoc-equal (car expr) extra-fn-list)))
         (cond
          (fn-entry
           ;; Uninterpretted function
           (let* ((rev-sig (revappend (cdr fn-entry) nil))
                  (ret-type (car rev-sig)))
             (mv (bv-type-size ret-type)
                 `(,(car expr) . ,args))))
          (t
           ;;(let ((var-entry (assoc-equal (car expr) var-alist)))
           ;;  (cond
           ;;   ((and (not args) var-entry)
           ;;    ;; A function with no arguments IS a variable
           ;;    (mv (ve-sz var-entry) (ve-expr var-entry)))
           ;;   (t
           (mv 0
               (er hard 'smt-to-acl2-expr
                   "Unsupported expression: ~x0~%" expr)))))))))))
)

(defun smt-to-acl2 (smt-expr extra-fn-list var-alist)
  (mv-let
   (bv-sz acl2-expr)
   (smt-to-acl2-expr smt-expr extra-fn-list var-alist)
   (declare (ignore bv-sz))
   acl2-expr))

(defun raw-sig-alist (extra-fn-list acc)
  (cond
   ((endp extra-fn-list)
    acc)
   (t
    (raw-sig-alist (cdr extra-fn-list)
                   (cons (cons (symbol-from-sym-str (caar extra-fn-list) "-RAW")
                               (cdar extra-fn-list))
                         acc)))))

(defabbrev msg-info-file-name (msg-info)
  (cdr msg-info))

(defabbrev msg-info-expected-ans (msg-info)
  (car msg-info))

(defabbrev make-msg-info (expected-ans file-name)
  (cons expected-ans file-name))

(defabbrev update-msg-info-expected-ans (expected-ans msg-info)
  (cons expected-ans (msg-info-file-name msg-info)))

(defun output-thm (assumpt-list formula extra-fn-list msg-info channel state)
  (let* (;;(formula `(implies (and . ,assumpt-list) ,conc))
         ;;(formula `(implies ,(and-macro assumpt-list) ,conc))
         ;;(extra-raw-fn-list (raw-sig-alist extra-fn-list nil))

         ;;(hints `((sat-plus-when-stable
         ;;          stable-under-simplificationp
         ;;          '(:extrafuns ,(raw-sig-alist extra-fn-list nil))
         ;;          '(theory (quote raw-bv-theory)))))
         ;;(state (print-bv-object '(comp t) channel state))
         (obj `(smt-check ,assumpt-list
                          ,formula
                          ,(raw-sig-alist extra-fn-list nil)
                          raw-bv-theory
                          ,(msg-info-expected-ans msg-info)
                          ,(msg-info-file-name msg-info))))
    (print-bv-object obj channel state)))

(defun preds2funs (extrapreds extra-fn-list)
  (cond
   ((endp extrapreds)
    extra-fn-list)
   (t
    (let* ((pred (car extrapreds))
           (name (car pred))
           (rev-args (revappend (cdr pred) nil))
           (sig (cons name (revappend rev-args '(bool)))))
      (preds2funs (cdr extrapreds) (cons sig extra-fn-list))))))

(defun add-new-extrafuns (extrafuns extra-fn-list var-alist)
  (cond
   ((endp extrafuns)
    (mv extra-fn-list var-alist))
   ((equal (len (car extrafuns)) 2)
    ;; Functions with no inputs are variables!
    (let* ((fn-entry (car extrafuns))
           (fn (car fn-entry))
           (ret-type (cadr fn-entry))
           (sz (bv-type-size ret-type)))
      (add-new-extrafuns (cdr extrafuns)
                         (cons (car extrafuns) extra-fn-list)
                         (cons (make-var-entry fn sz (list fn)) ;;`(make-bv ,sz ,fn))
                               var-alist))))
   (t
    (add-new-extrafuns (cdr extrafuns)
                       (cons (car extrafuns) extra-fn-list)
                       var-alist))))

(defun translate-type (type)
  (cond
   ((eq type '|bool|)
    'bool)
   ((and (consp type) (eq (car type) '|BitVec|))
    (cons 'bitvec (cdr type)))
   (t
    (er hard 'translate-type
        "ERROR: Unrecognized type: ~x0~%" type))))

(defun translate-type-list (type-list acc)
  (cond
   ((endp type-list)
    (revappend acc nil))
   (t
    (translate-type-list (cdr type-list)
                         (cons (translate-type (car type-list))
                               acc)))))

(defun translate-sig (sig)
  (cons (car sig) (translate-type-list (cdr sig) nil)))

(defun translate-sigs (sig-list acc)
  (cond
   ((endp sig-list)
    acc)
   (t
    (translate-sigs (cdr sig-list)
                    (cons (translate-sig (car sig-list))
                          acc)))))

(defun translate-expectation (expectation)
  (cond
   ((eq expectation '|unsat|)
    'unsat)
   ((eq expectation '|sat|)
    'sat)
   (t
    (er hard 'translate-expection
        "ERROR: Unrecognized expectation: ~x0~%" expectation))))

(defun write-smt-cmd-list (smt-cmd-list assumpt-list extra-fn-list var-alist msg-info channel state)
  (cond
   ((endp smt-cmd-list)
    state)
   ((equal (car smt-cmd-list) '|:status|)
    (let ((expected-ans (translate-expectation (cadr smt-cmd-list))))
      (write-smt-cmd-list (cddr smt-cmd-list)
                          assumpt-list
                          extra-fn-list
                          var-alist
                          (update-msg-info-expected-ans expected-ans msg-info)
                          channel
                          state)))

   ((equal (car smt-cmd-list) '|:extrafuns|)
    (let* ((extrafuns (cadr smt-cmd-list))
           (extrafuns (translate-sigs extrafuns nil)))
      (mv-let
       (extra-fn-list var-alist)
       (add-new-extrafuns extrafuns extra-fn-list var-alist)
       (write-smt-cmd-list (cddr smt-cmd-list)
                           assumpt-list
                           extra-fn-list
                           var-alist
                           msg-info
                           channel
                           state))))

   ((equal (car smt-cmd-list) '|:extrapreds|)
    (let* ((extrapreds (cadr smt-cmd-list))
           (extrapreds (translate-sigs extrapreds nil))
           (extrafuns (preds2funs extrapreds nil)))
      (mv-let
       (extra-fn-list var-alist)
       (add-new-extrafuns extrafuns extra-fn-list var-alist)
       (write-smt-cmd-list (cddr smt-cmd-list)
                           assumpt-list
                           extra-fn-list
                           var-alist
                           msg-info
                           channel
                           state))))

   ((equal (car smt-cmd-list) '|:assumption|)
    (let* ((smt-assumpt (cadr smt-cmd-list))
           (acl2-assumpt (smt-to-acl2 smt-assumpt extra-fn-list var-alist)))
           ;;(acl2-assumpt `(b-hyp ,acl2-assumpt)))
      (write-smt-cmd-list (cddr smt-cmd-list)
                          (cons acl2-assumpt assumpt-list)
                          extra-fn-list
                          var-alist
                          msg-info
                          channel
                          state)))

   ((equal (car smt-cmd-list) '|:formula|)
    (mv-let
     (sigs state)
     (output-defstubs extra-fn-list nil channel state)
     (let* ((state (output-sig-events sigs channel state))
            (smt-conc (cadr smt-cmd-list))
            (acl2-conc (smt-to-acl2 smt-conc extra-fn-list var-alist))
            (state (output-thm assumpt-list acl2-conc
                               extra-fn-list msg-info channel state)))
       state)))
   (t
    (write-smt-cmd-list (cdr smt-cmd-list) assumpt-list extra-fn-list var-alist
                        msg-info channel state))))

(defun write-acl2-file (smt-cmd-list msg-file channel state)
  (let* (;;(obj `(include-book ,(concat-str *sulfa-dir* "/books/bv-smt-solver/smt" )
         ;;                    :skip-proofs-okp t
         ;;                    :ttags (sat-ttag)))
         ;;(state (print-bv-object obj channel state))
         (state (write-smt-cmd-list smt-cmd-list nil nil nil
                                    (make-msg-info 'UNKNOWN msg-file)
                                    channel state)))
    state))

;; Translate an smt benchmark file from the SMT-lib format
;; into an ACL2 file.
(defun translate-smt-file (smt-file acl2-file msg-file state)
  (mv-let
   (obj state)
   (read-smt-file smt-file state)
   (mv-let
    (channel state)
    (open-output-channel acl2-file :character state)
    (let* ((state (write-acl2-file (cddr obj) msg-file channel state))
           (state (close-output-channel channel state)))
      state))))

(logic)

;; (translate-smt-file "egt-prepped-out.smt" "egt-acl2.lisp" "out.sof" state)
;; (translate-smt-file "egt-3349-prepped.smt" "egt-3349-acl2.lisp" "out.sof" state)
;; (translate-smt-file "egt-0003-prepped.smt" "egt-0003.lisp" "out.sof" state)
;; (translate-smt-file "egt-0000.psmt" "egt-0000.lisp" "out.sof" state)

;; Hard! Problems
;; (translate-smt-file "egt-4619.psmt" "egt-4619.lisp" "out.sof" state)
;; (translate-smt-file "egt-4717.psmt" "egt-4717.lisp" "out.sof" state)

;; (translate-smt-file "bitvec8.psmt" "bitvec8.lisp" "out.sof" state)

;; (translate-smt-file "bitvec6.smt.prepped" "bitvec6.lisp" "out.sof" state)
;; (translate-smt-file "bitops0.smt.prepped" "bitops0.lisp" "out.sof" state)

;; (translate-smt-file "bit-counting.smt.prepped" "bit-counting.lisp" "out.sof"state)
;; (translate-smt-file "egt-1520.smt.prepped" "egt-1520.lisp" "out.sof" state)
;; (translate-smt-file "egt-1047.smt.prepped" "egt-1047.lisp" "out.sof" state)
;; (translate-smt-file "egt-7394.smt.prepped" "egt-7394.lisp" "out.sof" state)

;; (setq si::*multiply-stacks* 16)


;; (translate-smt-file "bitops0.smt.prepped" "bitops0.lisp" "out.sof" state)
;; (translate-smt-file "egt-7394.smt.prepped" "egt-7394.lisp" "out.sof" state)
;; (translate-smt-file "bitvec0.smt.prepped" "bitvec0.lisp" "out.sof" state)


;; (translate-smt-file "egt-6812.smt.prepped" "egt-6812.lisp" "out.sof" state)

;; (translate-smt-file "bitvec7.smt.prepped" "bitvec7.lisp" "out.sof" state)
;; (include-book "translation" :ttags (sat-ttag))
;; (include-book "smt" :skip-proofs-okp t :ttags (sat-ttag))
