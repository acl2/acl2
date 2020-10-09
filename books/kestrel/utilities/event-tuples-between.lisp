; Event Tuple Utilities
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/definedp" :dir :system)
(include-book "kestrel/std/system/event-landmark-names" :dir :system)
(include-book "kestrel/std/system/function-symbol-listp" :dir :system)
(include-book "kestrel/std/system/function-symbolp" :dir :system)
(include-book "kestrel/std/system/irecursivep-plus" :dir :system)
(include-book "kestrel/std/system/logical-name-listp" :dir :system)
(include-book "kestrel/std/system/measure-plus" :dir :system)
(include-book "kestrel/std/system/pseudo-event-landmark-listp" :dir :system)
(include-book "kestrel/std/system/theorem-symbolp" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)
(include-book "kestrel/std/system/well-founded-relation-plus" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "system/pseudo-command-landmarkp" :dir :system)
(include-book "system/pseudo-event-landmarkp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a utility, EVENT-TUPLE-BETWEEN,
; to collect all the event tuples in the ACL2 world that are "between"
; (i) a set of functions and (ii) a set of functions and theorems,
; in the sense that they depend on set (i) and that set (ii) depends on them.
; This utility is somewhat preliminary;
; it may be improved or superseded altogether.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Recognize symbols that name functions or theorems.

(define fun-or-thm-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  (or (function-symbolp sym wrld)
      (theorem-symbolp sym wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Recognize NIL-terminated lists of symbols that name functions or theorems.

(define fun-or-thm-symbol-listp ((syms symbol-listp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  (cond ((atom syms) (eq syms nil))
        (t (and (fun-or-thm-symbolp (car syms) wrld)
                (fun-or-thm-symbol-listp (cdr syms) wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extract list of function symbols from list of symbols.

(define fun-symbols-of-symbols ((syms symbol-listp) (wrld plist-worldp))
  :returns (funs symbol-listp :hyp :guard)
  (if (endp syms)
      nil
    (let ((sym (car syms)))
      (if (function-symbolp sym wrld)
          (cons sym (fun-symbols-of-symbols (cdr syms) wrld))
        (fun-symbols-of-symbols (cdr syms) wrld))))
  ///

  (defthm function-symbol-listp-of-fun-symbols-of-symbols
    (implies (symbol-listp syms)
             (let ((funs (fun-symbols-of-symbols syms wrld)))
               (and (symbol-listp funs)
                    (function-symbol-listp funs wrld))))
    :hints (("Goal" :in-theory (enable function-symbol-listp
                                       function-symbolp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function references another function iff
; its body, measure, well-founded relation, or guard does.
; The following code returns the set of functions referenced by a function.
; We only handle defined functions for now:
; we stop with an error if we encounter a non-defined function.

(define funs-in-fun ((fun symbolp) (wrld plist-worldp))
  :guard (function-symbolp fun wrld)
  ;; :returns (funs symbol-listp)
  :mode :program
  (if (not (definedp fun wrld))
      (raise "Non-defined function ~x0 not supported." fun)
    (union-eq (all-ffn-symbs (ubody fun wrld) nil)
              (if (and (logicp fun wrld)
                       (irecursivep+ fun wrld))
                  (union-eq (all-ffn-symbs (measure+ fun wrld) nil)
                            (list (well-founded-relation+ fun wrld)))
                nil)
              (all-ffn-symbs (guard fun nil wrld) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A set of functions FS references a function F iff
; any function in FS references F.
; The following code returns the set of functions F referenced by FS.

(define funs-in-funs ((funs symbol-listp) (wrld plist-worldp))
  :guard (function-symbol-listp funs wrld)
  ;; :returns (funs2 symbol-listp)
  :mode :program
  (if (endp funs)
      nil
    (union-eq (funs-in-fun (car funs) wrld)
              (funs-in-funs (cdr funs) wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A theorem references a function iff its formula does.
; The following code returns the set of functions referenced by a theorem.

(define funs-in-thm ((thm symbolp) (wrld plist-worldp))
  :guard (theorem-symbolp thm wrld)
  ;; :returns (funs symbol-listp)
  :mode :program
  (all-ffn-symbs (formula thm nil wrld) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Each event tuple introduces zero or more functions.
; Only DEFUN, DEFUNS, and ENCAPSULATE events introduce functions.

(define event-tuple-functions ((eventup pseudo-event-landmarkp))
  ;; returns SYMBOL-LISTP
  :mode :program
  (let ((type (access-event-tuple-type eventup)))
    (if (member type '(defun defuns encapsulate))
        (event-landmark-names eventup)
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Return the first N event tuples (in the event landmark triples) in the world,
; or all of them if the world has fewer than N.
; Meant for interactive use,
; to inspect the most recent event tuples in the world.

(define first-n-event-tuples ((n natp) (wrld plist-worldp))
  ;; :returns (eventups pseudo-event-landmark-listp :hyp :guard)
  :mode :program
  (if (or (zp n)
          (endp wrld))
      nil
    (let ((triple (car wrld)))
      (if (eq (car triple) 'event-landmark)
          (if (eq (cadr triple) 'global-value) ; should be always true
              (let ((eventup (cddr triple)))
                (if (pseudo-event-landmarkp eventup) ; should be always true
                    (cons eventup (first-n-event-tuples (- n 1) (cdr wrld)))
                  (raise "Unexpected event tuple ~x0." eventup)))
            (raise "Unexpected event landmark triple ~x0." triple))
        (first-n-event-tuples n (cdr wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Return the first N command tuples (in the command landmark triples)
; in the world,
; or all of them if the world has fewer than N.
; Meant for interactive use,
; to inspect the most recent command tuples in the world.

(define first-n-command-tuples ((n natp) (wrld plist-worldp))
  ;; :returns (commandtups pseudo-command-landmark-listp :hyp :guard)
  :mode :program
  (if (or (zp n)
          (endp wrld))
      nil
    (let ((triple (car wrld)))
      (if (eq (car triple) 'command-landmark)
          (if (eq (cadr triple) 'global-value) ; should be always true
              (let ((commandtup (cddr triple)))
                (if (pseudo-command-landmarkp
                     commandtup) ; should be always true
                    (cons commandtup
                          (first-n-command-tuples (- n 1) (cdr wrld)))
                  (raise "Unexpected command tuple ~x0." commandtup)))
            (raise "Unexpected command landmark triple ~x0." triple))
        (first-n-command-tuples n (cdr wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Remove from the world all the triples
; that chronologically follow the event tuples
; that introduce the given logical names.
; Recall that the world list is in reverse chronological order
; (most recent triple first).
; We scan the list until we find an event tuple that introduces
; any of the given logical names;
; the event tuples for the other given logical names (if any)
; must occur later in the list (i.e. chronologically earlier).

(define remove-world-triples-after (names (wrld plist-worldp))
  :guard (logical-name-listp names wrld)
  ;; returns PLIST-WORLDP
  :mode :program
  (if (endp wrld)
      (raise "Unexpected: world has no event tuples for ~x0." names)
    (let ((triple (car wrld)))
      (if (eq (car triple) 'event-landmark)
          (if (eq (cadr triple) 'global-value) ; should be always true
              (if (intersectp (event-landmark-names (cddr triple)) names)
                  wrld ; found, done
                (remove-world-triples-after names (cdr wrld))) ; keep going
            (raise "Unexpected event landmark triple ~x0." triple))
        (remove-world-triples-after names (cdr wrld)))))) ; keep going

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extract from the world the shortest list of most recent event tuples,
; that introduce all of the given logical names.
; We scan the list of world triples, and collect all the event tuples,
; until we have collected event tuples for all of the given logical names.
; Thus, the result is a prefix (given the reverse chronological order)
; of the world.
; We use an accumulator in the tail recursion,
; so the event tuples are collected in chronological order (most recent last),
; which is reversed compared to the list of world triples.

(define event-tuples-with-names-aux
  ((names consp) (wrld plist-worldp) (eventups pseudo-event-landmark-listp))
  :guard (logical-name-listp names wrld)
  ;; returns PSEUDO-EVENT-LANDMARK-LISTP, in chronological order
  :mode :program
  (if (endp wrld)
      (raise "Unexpected: world has no event tuples for ~x0." names)
    (let ((triple (car wrld)))
      (if (eq (car triple) 'event-landmark)
          (if (eq (cadr triple) 'global-value) ; should be always true
              (let* ((eventup (cddr triple))
                     (eventups (cons eventup eventups)) ; collect event tuples
                     (names ; remove any found names from to-be-found list
                      (set-difference$ names (event-landmark-names eventup))))
                (if (eq names nil)
                    eventups ; no more names to collect event tuples for, done
                  (event-tuples-with-names-aux
                   names
                   (cdr wrld) eventups))) ; keep going
            (raise "Unexpected event landmark triple ~x0." triple))
        (event-tuples-with-names-aux names
                                     (cdr wrld) eventups))))) ; keep going

(define event-tuples-with-names ((names consp) (wrld plist-worldp))
  :guard (logical-name-listp names wrld)
  ;; returns PSEUDO-EVENT-LANDMARK-LISTP, in chronological order
  :mode :program
  (event-tuples-with-names-aux names wrld nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We say that
; an event tuple E directly references a set of functions FS = {F1,...,Fn}
; exactly in the following cases:
; - E is a DEFUN event tuple
;   whose function is in FS or calls some function in FS.
; - E is a DEFUNS event tuple such that
;   at least one its functions is in FS or calls some function in FS.
; - E is a DEFTHM or DEFAXIOM event tuple
;   whose formula calls some function in FS.
; - E is a VERIFY-GUARD event tuple
;   for some function in FS.

; If E is an ENCAPSULATE,
; it may introduce functions that are in FS or call functions in FS,
; but for now we do not handle that:
; we stop with an error if E is an ENCAPSULATE event tuple
; that introduces some function(s)
; (but not if the ENCAPSULATE introduces no functions).
; This will need to be changed in the future.

; For now we do not handle functions introduced by DEFCHOOSE.
; If E is a DEFCHOOSE, we stop with an error.
; This will need to be changed in the future.

(define event-tuple-refs-funs-p
  ((eventup pseudo-event-landmarkp) (funs symbol-listp) (wrld plist-worldp))
  :guard (function-symbol-listp funs wrld)
  ;; returns BOOLEANP
  :mode :program
  (case (access-event-tuple-type eventup)
    ((defun defuns)
     (let ((names (event-landmark-names eventup)))
       (or (intersectp funs names)
           (intersectp funs (funs-in-funs names wrld)))))
    ((defthm defaxiom)
     (let ((name (car (event-landmark-names eventup))))
       (intersectp funs (funs-in-thm name wrld))))
    (verify-guards
      (let ((form (access-event-tuple-form eventup)))
        (member (cadr form) funs)))
    (encapsulate
      (if (event-landmark-names eventup) ; ENCAPSULATE introduces functions
          (progn$ (cw "ENCAPSULATE event tuple ~x0 not fully supported.~%~x1~%"
                      eventup (event-landmark-names eventup))
                  nil)
        nil))
    (defchoose
      (raise "DEFCHOOSE event tuple ~x0 not supported." eventup))
    (otherwise nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Given a list of event tuples and a set FS = {F1,...,Fn} of functions,
; the following code filters the list if event tuples
; to remove the ones that do not reference FS directly or indirectly,
; i.e. to retain only the event tuples that reference FS directly or indirectly.

; The list is assumed to be in chronological order (i.e. most recent last),
; which is opposite to the order in the ACL2 world (i.e. most recent first).
; The code scans the list,
; accumulating the retained event tuples in reverse chronological order
; (i.e. most recent first, as in the ACL2 world).
; In order to handle indirect references to FS
; (e.g. FS is directly referenced by F, which is directly referenced by F'),
; the code also accumulates the retained functions, starting from FS
; (e.g. as the event tuple of F is retained because F directly references FS,
; F is added to this accumulator,
; so when F' is processed, its event tuple is also retained as it should).

; When a DEFUN event tuple is encountered
; whose function has been introduced by a DEFINE-SK,
; the next 5 event tuples are removed (i.e. not retained).
; A DEFINE-SK generates a number of event tuples,
; including the DEFUN for the function introduced by DEFINE-SK,
; followed by 5 other event tuples.
; The DEFUN event tuple suffices to retain informaton about the function,
; so the other event tuples are not retained.
; Removing these other event tuples removes the ENCAPSULATE event tuple
; that introduces the witness for the function:
; given the current definition of EVENT-TUPLE-REFS-FUNS-P above,
; removing that ENCAPSULATE event tuple is necessary to avoid an error.

(define event-tuples-that-ref-funs-aux
  ((eventups
    pseudo-event-landmark-listp
    ;; event tuples to be filtered, in chronological order
    )
   (retained
    pseudo-event-landmark-listp
    ;; retained event tuples, in reverse chronological order
    )
   (funs symbol-listp) ; FS + functions that reference FS directly or indirectly
   (wrld plist-worldp))
  :guard (function-symbol-listp funs wrld)
  ;; returns PSEUDO-EVENT-LANDMARK-LISTP, in reverse chronological order
  :mode :program
  (if (endp eventups)
      retained
    (let* ((eventup (car eventups))
           (retainp (event-tuple-refs-funs-p eventup funs wrld))
           (eventups (cdr eventups))
           (eventups
            (if (and (eq (access-event-tuple-type eventup) 'defun)
                     (std::find-define-sk-guts
                      (access-event-tuple-namex eventup) wrld))
                (if (>= (len eventups) 5)
                    (nthcdr 5 eventups) ; remove next 5 event tuples (see above)
                  (raise
                   "Unexpected: fewer than 5 event tuples after function ~x0~
                    introduced by DEFINE-SK."
                   (access-event-tuple-namex eventup)))
              eventups))
           (retained (if retainp
                         (cons eventup retained)
                       retained))
           (funs (if retainp
                     (union-eq funs (event-tuple-functions eventup))
                   funs)))
      (event-tuples-that-ref-funs-aux eventups retained funs wrld))))

(define event-tuples-that-ref-funs
  ((eventups
    pseudo-event-landmark-listp
    ;; event tuples to be filtered, in chronological order
    )
   (funs symbol-listp) ; FS
   (wrld plist-worldp))
  :guard (function-symbol-listp funs wrld)
  ;; returns PSEUDO-EVENT-LANDMARK-LISTP, in reverse chronological order
  :mode :program
  (event-tuples-that-ref-funs-aux eventups nil funs wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consider a set of functions FS = {F1,...,Fn}
; and a set of functions and theorems GS = {G1,...,Gm},
; where each Gj chronologically follows each Fi.
; The following code returns the list of event tuples from the world
; that depend on the elements of FS and that the elements of GS depend on;
; the list includes the event tuples that introduce the elements of FS and GS.

; The list of event tuples is calculated via the following steps:
; 1. Remove from the world all the triples that chronologically follow GS.
; 2. Extract, from the resulting list of triples,
;    the shortest prefix of event tuples that include FS.
;    The resulting event tuples
;    include all the ones that depend on FS and that GS depend on,
;    but may include others.
; 3. Remove from the list of event tuples those that do not depend on FS.
;    The resulting event tuples all depend on FS,
;    but GS may not depend on all of them.

(define event-tuples-between-reversed
  ((funs symbol-listp) ; FS
   (funs-thms symbol-listp) ; GS
   (wrld plist-worldp))
  :guard (and (function-symbol-listp funs wrld)
              (fun-or-thm-symbol-listp funs-thms wrld))
  ;; returns PSEUDO-EVENT-LANDMARK-LISTP, in reverse chronological order
  :mode :program
  (let* ((triples (remove-world-triples-after funs-thms wrld)) ; step 1
         (eventups (event-tuples-with-names funs triples))) ; step 2
    (event-tuples-that-ref-funs eventups funs wrld))) ; step 3

(define event-tuples-between
  ((funs symbol-listp) ; FS
   (funs-thms symbol-listp) ; GS
   (wrld plist-worldp))
  :guard (and (function-symbol-listp funs wrld)
              (fun-or-thm-symbol-listp funs-thms wrld))
  ;; returns PSEUDO-EVENT-LANDMARK-LISTP, in chronological order
  :mode :program
  (reverse (event-tuples-between-reversed funs funs-thms wrld)))
