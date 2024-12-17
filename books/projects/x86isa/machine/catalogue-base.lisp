; x86isa categorized listings of implemented/unimplemented instructions
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

(in-package "X86ISA")

(include-book "inst-listing")



(local (in-theory (disable inst-list-p-of-maps)))

(define find-insts-named ((names symbol-listp)
                          (inst-list inst-list-p))
  :returns (unimp-insts inst-list-p)
  (b* (((when (atom inst-list))
        nil)
       ((inst inst) (car inst-list))
       ((when (member-symbol-name (if (stringp inst.mnemonic)
                                      inst.mnemonic
                                    (symbol-name inst.mnemonic))
                                  names))
        (cons (inst-fix inst)
              (find-insts-named names (cdr inst-list)))))
    (find-insts-named names (cdr inst-list))))

(define find-insts-named-str ((names string-listp)
                              (inst-list inst-list-p))
  :returns (unimp-insts inst-list-p)
  (b* (((when (atom inst-list))
        nil)
       ((inst inst) (car inst-list))
       ((when (member-equal (if (stringp inst.mnemonic)
                                inst.mnemonic
                              (symbol-name inst.mnemonic))
                            names))
        (cons (inst-fix inst)
              (find-insts-named-str names (cdr inst-list)))))
    (find-insts-named-str names (cdr inst-list))))

(define keep-implemented-insts ((inst-list inst-list-p))
  :returns (impl-insts inst-list-p)
  (if (atom inst-list)
      nil
    (if (inst->fn (car inst-list))
        (cons (inst-fix (car inst-list))
              (keep-implemented-insts (cdr inst-list)))
      (keep-implemented-insts (cdr inst-list)))))

(define keep-unimplemented-insts ((inst-list inst-list-p))
  :returns (unimpl-insts inst-list-p)
  (if (atom inst-list)
      nil
    (if (inst->fn (car inst-list))
        (keep-unimplemented-insts (cdr inst-list))
      (cons (inst-fix (car inst-list))
            (keep-unimplemented-insts (cdr inst-list))))))




(define section-number-< ((x nat-listp)
                          (y nat-listp))
  (cond ((atom y)    nil)
        ((atom x)    t)
        ((< (car x) (car y)) t)
        ((< (car y) (car x)) nil)
        (t (section-number-< (cdr x) (cdr y)))))


(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/strpos" :dir :system)

(define parse-section-number-aux ((strs string-listp))
  (if (atom strs)
      nil
    (cons (str::strval (car strs))
          (parse-section-number-aux (cdr strs)))))

(define parse-section-number ((str stringp))
  :returns (secnum nat-listp)
  (b* ((lst (parse-section-number-aux (str::strtok str '(#\.)))))
    (if (nat-listp lst)
        lst
      (raise "Bad section number: ~s0" str))))

(define parse-section-heading ((heading stringp))
  :returns (mv (secnum nat-listp)
               (title stringp))
  (b* ((space-idx (str::strpos " " heading))
       ((unless space-idx)
        (mv nil (mbe :logic (if (stringp heading) heading "")
                     :exec heading)))
       (secnum (parse-section-number (subseq heading 0 space-idx)))
       (title (subseq heading (+ 1 space-idx) nil)))
    (mv secnum title)))


(defconst *all-opcode-maps*
  (append *one-byte-opcode-map*
          *two-byte-opcode-map*
          *0f-38-three-byte-opcode-map*
          *0f-3a-three-byte-opcode-map*))

(make-event
 `(define all-opcode-maps ()
    :inline t
    :no-function t
    :returns (insts inst-list-p)
    ',*all-opcode-maps*
    ///
    (in-theory (disable (all-opcode-maps)))))

(define inst-list->mnemonics ((insts inst-list-p))
  :Returns (mnemonics)
  :prepwork ((local (in-theory (disable acl2::member-of-cons member-equal))))
  (if (atom insts)
      nil
    (cons (inst->mnemonic (car insts))
          (inst-list->mnemonics (cdr insts)))))

(define keep-strings (x)
  :returns (strings string-listp)
  (if (atom x)
      nil
    (if (stringp (car x))
        (cons (car x) (keep-strings (cdr x)))
      (keep-strings (cdr x)))))

(make-event
 `(define all-mnemonics ()
    :returns (mnemonics string-listp)
    ',(keep-strings (inst-list->mnemonics (all-opcode-maps)))
    ///
    (in-theory (disable (all-mnemonics)))))

(encapsulate nil
  (local (in-theory (disable inst-list-p acl2::member-of-cons member-equal)))
  (fty::deflist inst-list :elt-type inst :true-listp t))

(fty::deftypes sdm-instruction-table
  (defprod sdm-instruction-table-entry
    ((title stringp)
     (implemented inst-list-p)
     (unimplemented inst-list-p)
     (doc stringp)
     (subsecs sdm-instruction-table))
    :layout :alist
    :measure (+ (* 2 (acl2-count x)) 1))
  (fty::defmap sdm-instruction-table
    :key-type nat-listp
    :val-type sdm-instruction-table-entry
    :true-listp t
    :measure (* 2 (acl2-count x)))
  ///
  (defthm len-of-sdm-instruction-table-fix
    (<= (len (sdm-instruction-table-fix x)) (len x))
    :hints(("Goal" :induct (len x)
            :expand ((sdm-instruction-table-fix x))))
    :rule-classes :linear))



(define sdm-instruction-table-implemented-instructions ((x sdm-instruction-table-p))
  :measure (sdm-instruction-table-count x)
  :returns (impl inst-list-p)
  (b* ((x (sdm-instruction-table-fix x))
       ((when (atom x)) nil)
       ((sdm-instruction-table-entry entry) (cdar x))
       (sub-impl (sdm-instruction-table-implemented-instructions entry.subsecs)))
    (append entry.implemented sub-impl
            (sdm-instruction-table-implemented-instructions (cdr x)))))

(define sdm-instruction-table-unimplemented-instructions ((x sdm-instruction-table-p))
  :measure (sdm-instruction-table-count x)
  :returns (unimpl inst-list-p)
  (b* ((x (sdm-instruction-table-fix x))
       ((when (atom x)) nil)
       ((sdm-instruction-table-entry entry) (cdar x))
       (sub-unimpl (sdm-instruction-table-unimplemented-instructions entry.subsecs)))
    (append entry.unimplemented sub-unimpl
            (sdm-instruction-table-unimplemented-instructions (cdr x)))))

(defconst *def-sdm-instruction-section-verbose* nil)

(define symbol-list->names ((x symbol-listp))
  :returns (names string-listp)
  (if (atom x)
      nil
    (cons (symbol-name (car x))
          (symbol-list->names (cdr x)))))


(defines eval-feature-expr
  (define eval-feature-expr (expr
                             (inst inst-p))
    :measure (acl2-count expr)
    (if (atom expr)
        (and expr
             (or (eq expr t)
                 (and (symbolp expr)
                      (case expr
                        (:vex (opcode->vex (inst->opcode inst)))
                        (:vex-256 (and (opcode->vex (inst->opcode inst))
                                       (member-eq :|256| (opcode->vex (inst->opcode inst)))))
                        (:vex-128 (and (opcode->vex (inst->opcode inst))
                                       (member-eq :|256| (opcode->vex (inst->opcode inst)))))
                        (:evex (opcode->evex (inst->opcode inst)))
                        (:no-vex (b* ((opcode (inst->opcode inst)))
                                   (and (not (opcode->vex opcode))
                                        (not (opcode->evex opcode)))))
                        (:rex-w (eq (opcode->rex (inst->opcode inst)) :w))
                        (t (member-eq expr (opcode->feat (inst->opcode inst))))))
                 (equal expr (inst->mnemonic inst)))
             t)
      (case-match expr
        (('not sub) (not (eval-feature-expr sub inst)))
        ((op . exprlist)
         (if (member-eq op '(and or xor))
             (eval-feature-expr-lst op exprlist inst)
           (raise "bad expr: ~x0~%" expr)))
        (& (raise "bad expr: ~x0~%" expr)))))
  (define eval-feature-expr-lst (op
                                 exprs
                                 (inst inst-p))
    :guard (member-eq op '(and or xor))
    :measure (acl2-count exprs)
    (b* (((when (atom exprs)) (eq op 'and))
         (first (eval-feature-expr (car exprs) inst)))
      (case op
        (and (and first
                  (eval-feature-expr-lst op (cdr exprs) inst)))
        (or (or first
                (eval-feature-expr-lst op (cdr exprs) inst)))
        (t (xor first
                (eval-feature-expr-lst op (cdr exprs) inst)))))))

(define keep-insts-satisfying-feature (expr
                                       (insts inst-list-p))
  :returns (new-insts inst-list-p)
  (b* (((when (atom insts)) nil)
       ((inst inst) (car insts)))
    (if (eval-feature-expr expr inst)
        (cons (inst-fix inst)
              (keep-insts-satisfying-feature expr (cdr insts)))
      (keep-insts-satisfying-feature expr (cdr insts)))))



(define sdm-instruction-pair-p (x)
  (and (consp x)
       (nat-listp (car x))
       (sdm-instruction-table-entry-p (cdr x)))
  ///
  (defthm sdm-instruction-pair-p-when-reqs
    (implies (and (nat-listp (car x))
                  (sdm-instruction-table-entry-p (cdr x)))
             (sdm-instruction-pair-p x))))

(define sdm-instruction-pair-< ((x sdm-instruction-pair-p)
                                (y sdm-instruction-pair-p))
  :prepwork ((local (in-theory (enable sdm-instruction-pair-p))))
  (section-number-< (car X) (car y)))

(encapsulate nil
  (local (in-theory (enable sdm-instruction-pair-<
                            sdm-instruction-pair-p
                            section-number-<)))

  (local (defthm section-number-<-transitive
           (implies (and (section-number-< x y)
                         (section-number-< y z))
                    (section-number-< x z))))

  (local (defthm section-number->=-transitive
           (implies (and (not (section-number-< x y))
                         (not (section-number-< y z)))
                    (not (section-number-< x z)))))

  (local (defthm section-number-<-irreflexive
           (not (section-number-< x x))))

  (local (in-theory (disable section-number-<)))

  (acl2::defsort sdm-instruction-table-sort
    :prefix sdm-instruction-table
    ;; :comparable-listp sdm-instruction-table-p
    :compare< sdm-instruction-pair-<
    :comparablep sdm-instruction-pair-p
    :true-listp t)

  (defthm sdm-instruction-table-list-p-is-sdm-instruction-table-p
    (equal (sdm-instruction-table-list-p x)
           (sdm-instruction-table-p x))
    :hints(("Goal" :in-theory (enable sdm-instruction-table-p
                                      sdm-instruction-table-list-p))))

  (defthm sdm-instruction-table-p-of-insertsort
    (implies (sdm-instruction-table-p x)
             (sdm-instruction-table-p (sdm-instruction-table-insertsort x)))
    :hints (("goal" :use sdm-instruction-table-insertsort-creates-comparable-listp
             :in-theory (disable sdm-instruction-table-insertsort-creates-comparable-listp)))))



(define sdm-instruction-table-gather-subtopics ((prefix nat-listp)
                                        (x sdm-instruction-table-p))
  :returns (mv (prefixed-x sdm-instruction-table-p)
               (rest-x sdm-instruction-table-p))
  :measure (len x)
  :verify-guards nil
  (b* (((when (atom x)) (mv nil nil))
       ((unless (mbt (and (consp (car x))
                          (nat-listp (caar x)))))
        (sdm-instruction-table-gather-subtopics prefix (cdr x)))
       (x1-section (caar x))
       ((unless (acl2::prefixp (acl2::nat-list-fix prefix) x1-section))
        (mv nil (sdm-instruction-table-fix x)))
       ;; first element is still prefixed by the input prefix, continue with the rest
       ;; first gather all the elements that are prefixed by section:
       ((mv x1-subsecs rest-x) (sdm-instruction-table-gather-subtopics x1-section (cdr x)))
       ((sdm-instruction-table-entry entry) (cdar x))
       (new-x1 (cons x1-section (change-sdm-instruction-table-entry entry :subsecs (append entry.subsecs x1-subsecs))))
       ((unless (mbt (< (len rest-x) (len x))))
        (mv (list new-x1) rest-x))
       ((mv rest rest-x) (sdm-instruction-table-gather-subtopics prefix rest-x)))
    (mv (cons new-x1 rest) rest-x))
  ///
  (defret <fn>-rest-x-length
    (<= (len rest-x) (len x))
    :rule-classes :linear)

  (verify-guards sdm-instruction-table-gather-subtopics))

(define sdm-instruction-table-organize ((x sdm-instruction-table-p))
  ;; top level: sort, then gather subtopics
  :returns (organized sdm-instruction-table-p)
  (b* ((sorted (sdm-instruction-table-sort x))
       ((mv gathered &) (sdm-instruction-table-gather-subtopics nil sorted)))
    gathered))




(define def-sdm-instruction-section-fn ((header stringp)
                                        &key
                                        ((mnemonics symbol-listp) 'nil)
                                        ((instructions inst-list-p) 'nil)
                                        (features 't)
                                        (suppress-not-found 'nil)
                                        ((doc stringp) '""))
  (b* (((mv secnum title) (parse-section-heading header))
       (insts (append instructions (find-insts-named mnemonics (all-opcode-maps))))
       (insts (if (eq features t)
                  insts
                (keep-insts-satisfying-feature features insts)))
       (unimpl-insts (keep-unimplemented-insts insts))
       (impl-insts (keep-implemented-insts insts))
       (not-found-insts (set-difference-equal (symbol-list->names mnemonics)
                                              (inst-list->mnemonics insts)))
       (- (and not-found-insts
               (not suppress-not-found)
               (raise "Not found: ~x0~%" not-found-insts)))
       (entry (make-sdm-instruction-table-entry
               :title title
               :implemented impl-insts
               :unimplemented unimpl-insts
               :doc doc))
       (- (and *def-sdm-instruction-section-verbose*
               (cw "Entry: ~x0~%" entry))))
    `(table sdm-instruction-sect ',secnum ',entry)))

(defmacro def-sdm-instruction-section (&rest args)
  `(make-event (def-sdm-instruction-section-fn . ,args)))


