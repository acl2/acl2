

(in-package "ACL2")

;; This book introduces computed hints useful for when one wants to
;; systematically open up a cons structure and relieve proof
;; obligations about local properties.

;; At each step of the proof, the computed hint has a particular term
;; it is concentrating on. It will first delete any literals in the
;; current clause which do not mention that term.  It will then open
;; up any function which has that term as an argument.  When all such
;; functions have been expanded, it will heuristically choose to next
;; concentrate on either the CAR or CDR of that term based on (first)
;; which appears in the conclusion, and (if neither) which appear in
;; the rest of the clause.

;; We include two versions of the computed hint.  The first, which can
;; be invoked as (STRUCTURAL-DECOMP X) where X is the term to begin
;; decomposing, may lead to proof failure if at some point it
;; heuristically chooses the wrong term to concentrate on.  The
;; second, (STRUCTURAL-DECOMP-CAREFUL X), instead generates OR hints
;; at each heuristic decision, first trying the heuristic best guess,
;; then the other possible guess, and finally giving up.


(include-book "join-thms")

(include-book "tools/bstar" :dir :system)


(mutual-recursion
 (defun find-expands-for-arg-term (x arg world exclude)
   (cond ((atom x) nil)
         ((eq (car x) 'quote) nil)
         (t (let ((from-args (find-expands-for-arg-list
                              (cdr x) arg world exclude)))
              ;; If expansion is found in the args, don't expand x yet.
              (or from-args
                  (and (member-equal arg (cdr x))
                       ;; check that x is expandable:
                       (and (not (member (car x) exclude))
                            (or (consp (car x))
                                (getprop (car x) 'def-bodies nil
                                         'current-acl2-world world)))
                       (list x)))))))
 (defun find-expands-for-arg-list (x arg world exclude)
   (if (atom x)
       nil
     (union-equal (find-expands-for-arg-term (car x) arg world exclude)
                  (find-expands-for-arg-list (cdr x) arg world exclude)))))

(mutual-recursion
 (defun present-in-term (x subt)
   (cond ((equal x subt) t)
         ((atom x) nil)
         ((eq (car x) 'quote) nil)
         (t (present-in-term-list (cdr x) subt))))
 (defun present-in-term-list (x subt)
   (and (consp x)
        (or (present-in-term (car x) subt)
            (present-in-term-list (cdr x) subt)))))

(defun structure-decompose (x)
  (declare (ignore x)) t)

(in-theory (disable structure-decompose
                    (structure-decompose)
                    (:type-prescription structure-decompose)))

(defevaluator strdec-ev strdec-ev-lst
  ((if x y z) (structure-decompose x) (not x)))

(def-join-thms strdec-ev)

(defun remove-terms-without-present (clause struct)
  (if (atom clause)
      clause
    (let ((rest (remove-terms-without-present (cdr clause) struct)))
      (if (present-in-term (car clause) struct)
          (if (equal rest (cdr clause))
              clause
            (cons (car clause) rest))
        rest))))

(defthm strdec-ev-remove-terms-without-present
  (implies (strdec-ev (disjoin (remove-terms-without-present
                                clause struct))
                      alist)
           (strdec-ev (disjoin clause) alist)))

(defun select-expand-substruct (clause substruct)
  (list (cons `(not (structure-decompose ,substruct))
              (remove-terms-without-present clause substruct))))

(defun remove-irrel-cp (clause substruct)
  (list (remove-terms-without-present clause substruct)))

(defthm select-expand-substruct-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (strdec-ev (conjoin-clauses
                            (select-expand-substruct
                             clause substruct))
                           a))
           (strdec-ev (disjoin clause) a))
  :hints (("goal" :in-theory (enable structure-decompose)))
  :rule-classes :clause-processor)


(defthm remove-irrel-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (strdec-ev (conjoin-clauses
                            (remove-irrel-cp
                             clause substruct))
                           a))
           (strdec-ev (disjoin clause) a))
  :hints (("goal" :in-theory (enable structure-decompose)))
  :rule-classes :clause-processor)

(defun structural-decomp-hint-careful (clause arg stablep world exclude)
  (and stablep
       ;;(prog2$ (cw "Running structural-decomp-hint-careful, arg: ~x0~%" arg)
       (let ((expands (find-expands-for-arg-list clause arg world exclude)))
         (if expands
             `(:computed-hint-replacement
               ((structural-decomp-hint-careful
                 clause ',arg stable-under-simplificationp world ',exclude))
               :expand ,expands)
           ;; Heuristically decide based on presence in the conclusion
           ;; or in rest of clause whether to prefer expanding
           ;; (car arg) or (cdr arg)
           (b* ((car `(car ,arg))
                (cdr `(cdr ,arg))
                (concl (car (last clause)))
                ((mv 1st 2nd give-up)
                 (cond ((present-in-term concl car) (mv car cdr nil))
                       ((present-in-term concl cdr) (mv cdr car nil))
                       ((present-in-term-list clause car)
                        (mv car cdr nil))
                       ((present-in-term-list clause cdr)
                        (mv cdr car nil))
                       (t (mv car cdr t)))))
             (if give-up
                 (prog2$ (cw "Giving up on structural expansion~%")
                         '(:no-op t))
               `(:computed-hint-replacement
                 ((after-select-substruct-hint
                   clause stable-under-simplificationp world ',exclude))
                 :or ((:clause-processor
                       (select-expand-substruct clause ',1st))
                      (:clause-processor
                       (select-expand-substruct clause ',2nd))
                      (:no-op t)))))))))

(defun after-select-substruct-hint (clause stablep world exclude)
  ;; (prog2$ (cw "Running after-select-substruct-hint~%")
          (let ((term (car clause)))
            (case-match term
              (('not ('structure-decompose arg))
               (structural-decomp-hint-careful clause arg stablep world exclude))
              (t (prog2$ (cw "After-select-substruct-hint didn't find the
chosen structure to decompose. Clause: ~x0~%" clause)
                         '(:no-op t))))))

(defun structural-decomp-hint-fast (clause arg stablep world exclude)
  (and stablep
       ;;(prog2$ (cw "Running structural-decomp-hint-fast, arg: ~x0~%" arg)
       (let ((expands (find-expands-for-arg-list clause arg world exclude)))
         (if expands
             `(:computed-hint-replacement
               ((structural-decomp-hint-fast
                 clause ',arg stable-under-simplificationp world ',exclude))
               :expand ,expands)
           ;; Heuristically decide based on presence in the conclusion
           ;; or in rest of clause whether to prefer expanding
           ;; (car arg) or (cdr arg)
           (b* ((car `(car ,arg))
                (cdr `(cdr ,arg))
                (concl (car (last clause)))
                ((mv 1st give-up)
                 (cond ((present-in-term concl car) (mv car nil))
                       ((present-in-term concl cdr) (mv cdr nil))
                       ((present-in-term-list clause car)
                        (mv car nil))
                       ((present-in-term-list clause cdr)
                        (mv cdr nil))
                       (t (mv car t)))))
             (if give-up
                 (prog2$ (cw "Giving up on structural expansion~%")
                         '(:no-op t))
               `(:computed-hint-replacement
                 ((structural-decomp-hint-fast
                   clause ',1st stable-under-simplificationp world ',exclude))
                 :clause-processor
                 (remove-irrel-cp clause ',1st))))))))


(defmacro structural-decomp (arg &key do-not-expand)
  `(structural-decomp-hint-fast clause ',arg stable-under-simplificationp world
                                ,do-not-expand))

(defmacro structural-decomp-careful (arg &key do-not-expand)
  `(structural-decomp-hint clause ',arg stable-under-simplificationp world
                           ,do-not-expand))

