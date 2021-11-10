; A tool to prove specialized versions of existing theorems
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/terms-light/sublis-var-and-magic-eval" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)

;; TODO: Tolerate names of defuns when given among the names of defthms (should we specialize them?)

;; Returns a defthm
(defun specialize-theorem-fn (name
                              suffix
                              alist
                              state)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp suffix)
                              (symbol-alistp alist))
                  :stobjs state
                  :mode :program))
  (b* ((wrld (w state))
       (alist-cars (strip-cars alist))
       (alist-cdrs (strip-cdrs alist))
       (translated-alist-cdrs (translate-terms alist-cdrs 'specialize-theorem-fn wrld))
       (alist (pairlis$ alist-cars translated-alist-cdrs))
       (body (defthm-body name wrld))
       (body-vars (free-vars-in-term body))
       ((when (not (subsetp-equal alist-cars body-vars)))
        (er hard? 'specialize-theorem-fn "Attempt to specialize ~x0 with vars ~x1, not all of which are in the body, ~x2." name alist-cars body))
       (new-body (sublis-var-and-magic-eval alist body state)))
    `(defthm ,(pack$ name suffix)
       ,new-body
       ;; todo: rule-classes
       :hints (("Goal" :use (:instance ,name
                                       ;; this can be a problem if an alist key is not in the theorem
                                       ;; but another var with the same symbol name but a different package
                                       ;; is in the theorem
                                       ,@(alist-to-doublets alist))
                ;; Needed because we evaluate ground terms (with magic-eval):
                :in-theory (executable-counterpart-theory :here))))))

(defmacro specialize-theorem (name suffix alist)
  `(make-event (specialize-theorem-fn ,name ,suffix ,alist state)))

;; Returns a list of defthms.
(defun specialize-theorems-fn-aux (names suffix alist state)
  (declare (xargs :guard (and (symbol-listp names)
                              (symbolp suffix)
                              (symbol-alistp alist))
                  :stobjs state
                  :mode :program))
  (if (endp names)
      nil
    (cons (specialize-theorem-fn (first names) suffix alist state)
          (specialize-theorems-fn-aux (rest names) suffix alist state))))

;; Returns an event (a progn).
(defun specialize-theorems-fn (names suffix alist state)
  (declare (xargs :guard (and (symbol-listp names)
                              (symbolp suffix)
                              (symbol-alistp alist))
                  :stobjs state
                  :mode :program))
  `(progn ,@(specialize-theorems-fn-aux names suffix alist state)))

(defmacro specialize-theorems (names suffix alist)
  `(make-event (specialize-theorems-fn ,names ,suffix ,alist state)))

;move
(mutual-recursion
 (defun all-calls-in-term (target-fn term)
   (declare (xargs :guard (and (symbolp target-fn)
                               (pseudo-termp term))))
   (if (variablep term)
       nil
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           nil
         (let ((all-calls-in-args (all-calls-in-terms target-fn (fargs term))))
           (if (consp fn)
               (prog2$ (cw "Warning: not looking for calls in lambda body ~x0" term)
                       all-calls-in-args)
             (if (eq fn target-fn)
                 (cons term all-calls-in-args)
               all-calls-in-args)))))))

 (defun all-calls-in-terms (target-fn terms)
   (declare (xargs :guard (and (symbolp target-fn)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (append (all-calls-in-term target-fn (first terms))
             (all-calls-in-terms target-fn (rest terms))))))

;; Find all vars that are in the argum position (1-based) in the calls
(defun vars-at-argnum-position (calls argnum)
  (if (endp calls)
      nil
    (let* ((call (first calls))
           (arg (nth (+ -1 argnum) (fargs call))))
      (if (variablep arg)
          (cons arg (vars-at-argnum-position (rest calls) argnum))
        (vars-at-argnum-position (rest calls) argnum)))))

(defun add-checked-pairs-to-alist (keys vals alist)
  (declare (xargs :guard (and (alistp alist)
                              (true-listp keys)
                              (equal (len keys) (len vals)))))

  (if (endp keys)
      alist
    (let* ((key (first keys))
           (val (first vals))
           (binding (assoc-equal key alist)))
      (if binding
          (if (equal val (cdr binding))
              ;; existing binding is identical
              (add-checked-pairs-to-alist (rest keys) (rest vals) alist)
            (er hard? 'add-checked-pairs-to-alist "Conflicting binding, ~x0, found when trying to bind key ~x1 to ~x2." (cdr binding) key val))
        (add-checked-pairs-to-alist (rest keys) (rest vals) (acons key val alist))))))

(defun make-specialization-alist (triples body alist)
  (if (endp triples)
      alist
    (let* ((triple (first triples))
           (target-fn (first triple))
           (argnum (second triple))
           (val (third triple))
           (calls-in-body (all-calls-in-term target-fn body))
           (vars (vars-at-argnum-position calls-in-body argnum)))
      (make-specialization-alist (rest triples)
                                 body
                                 (add-checked-pairs-to-alist vars
                                                             (repeat (len vars) val)
                                                             alist)))))

;; Returns a list of 0 or 1 defthms
(defun specialize-calls-in-theorem (name suffix triples state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let* ((wrld (w state))
         (body (defthm-body name wrld))
         (alist (make-specialization-alist triples body nil)))
    (if alist
        ;; todo: this redoes some work!:
        (list (specialize-theorem-fn name suffix alist state))
      nil)))

;; Returns a list of defthms.
(defun specialize-calls-in-theorems-fn-aux (names
                                            suffix
                                            triples ; of the form (function argnum val)
                                            state
                                            )
  (declare (xargs :stobjs state
                  :mode :program))
  (if (endp names)
      nil
    (append (specialize-calls-in-theorem (first names) suffix triples state)
            (specialize-calls-in-theorems-fn-aux (rest names) suffix triples state))))

;; Returns an event (a progn).
(defun specialize-calls-in-theorems-fn (names
                                        suffix
                                        triples ; of the form (function argnum val)
                                        state
                                        )
  (declare (xargs :stobjs state
                  :mode :program))
  `(progn ,@(specialize-calls-in-theorems-fn-aux names suffix triples state)))

(defmacro specialize-calls-in-theorems (names suffix
                                              triples ; of the form (function argnum val)
                                              )
  `(make-event (specialize-calls-in-theorems-fn ,names ,suffix ,triples state)))
