; propagate-iso: A transformation to propagate an isomorphism from supplied isomorphic translations
;  of interface functions of a data type to their direct and indirect callers
;
; Copyright (C) 2016-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Stephen Westfold (westfold@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

; This book introduces propagate-iso, that applies an isomorphism to a series of events.
; This is based on propagate which propagates equality relationship rather than isomorphism.
; If you have a predicate p representing a datatype or domain along with primitive functions that
; operate on that datatype, and an isomorphism to another datatype p$1 with corresponding
; datatype functions then you can then call make-iso-events to create new versions of all
; of the functions that depend on p.  To distinguish these from the original
; functions, you supply a suffix, such as $1, to be appended to their names.
; If you don't want to propagate-iso to everything, you can specify a "top level"
; function, events after which will not be rebuilt.

; propagate-iso 1) proves that all of the new functions are isomorphic to the
; corresponding original functions and 2) proves that corresponding theorems about
; the original functions also hold about the new functions.

;todo: Add support for mutual recursion
;todo: Fix handling of defun-sk
;todo: adapt this to specs (see derivations/ dir)
;todo: recur into encapsulates?
;todo: think about macro expansion (use Matt's translate-raw?)
;todo: print the names of the generated functions

(include-book "../utilities/hints")
(include-book "utilities/deftransformation")
(include-book "kestrel/utilities/event-tuples-between" :dir :system)
(include-book "utilities/names")
;(include-book "transformation-table")
;(include-book "simplify-defun-impl")    ; just for generalize-to-lambda and fn-ubody
(include-book "../sequences/defmap")
(include-book "../sequences/deffilter")
(include-book "../std/system/pseudo-event-landmark-listp")

(include-book "misc/install-not-normalized" :dir :system)
(include-book "kestrel/std/util/defiso" :dir :system)
(include-book "kestrel/utilities/conjunctions" :dir :system)
(include-book "kestrel/utilities/defun-forms" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "tools/remove-hyps" :dir :system)
(include-book "kestrel/utilities/make-and-nice" :dir :system)

(include-book "kestrel/std/system/defun-sk-queries" :dir :system)

(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consider two isomorphic domains P1 and P2 (represented as predicates)
; with two isomorphisms P1-to-P2 and P2-to-P1 between them.
; Consider a function G1 that depends, directly or indirectly, on P1 values.
; For every function H1 that depends on P1 and that G1 depends on (including G1
; itself as a possible H1), we automatically generate an isomorphic version H2 of H1
; and a correctness theorem (in the case where H1 takes a single argument of domain P1
; and returns a value of domain P1 this is H1 x = P2-to-P1(H2(P1-to-P2 x)) ).
; H2 is obtained by replacing P1 with P2 and each previous H1' with its refinement H2',
; so the correctness theorem follows by substitution of equals for equals.
; For every theorem that depends on F1 or any H1, we automatically generate a
; corresponding theorem where F1 is replaced with F2 and each H1 with H2:
; the new theorem follows from the old one, by either using the previous hints with
; substitutions or by using the old theorem with substitutions using the isomorphisms
;  to map between P1 and P2 values.
; For every (VERIFY-GUARDS H1), we automatically generate a (VERIFY-GUARDS H2).

; The generation is performed by scanning the list of event tuples
; returned by event-tuples-between, with FS = {P1} and GS = {G1}.

(defthm list-mv-2
  (implies (and (true-listp e)
                (equal (len e) 2))
           (equal (list (mv-nth 0 e)
                        (mv-nth 1 e))
                  e))
  :hints (("Goal" :in-theory (enable mv-nth))))
(defthm list-mv-3
  (implies (and (true-listp e)
                (equal (len e) 3))
           (equal (list (mv-nth 0 e)
                        (mv-nth 1 e)
                        (mv-nth 2 e))
                  e)))

(defthm list-mv-4
  (implies (and (true-listp e)
                (equal (len e) 4))
           (equal (list (mv-nth 0 e)
                        (mv-nth 1 e)
                        (mv-nth 2 e)
                        (mv-nth 3 e))
                  e))
  :hints (("Goal" :use (:instance list-mv-3 (e (cdr e))) )))

(defconst *list-mv-thms* '(nil nil (list-mv-2) (list-mv-3) (list-mv-4)))


;; From simplify-defun-impl until (logic)
(program)
(defun get-def (fn wrld ev)

; We return the definition of fn in wrld, if any, without the leading defun.
; If there is no such definition, we return nil.

; Ev is optional.  If supplied, it is the value of (get-event fn wrld), which
; ideally is non-nil (else the call of get-event below will duplicate the work
; to find nil).

; This code is based on the definition of guard-raw in the ACL2 sources.

  (let ((ev (or ev (get-event fn wrld))))
    (case (car ev)
      (defun (cdr ev))
      (mutual-recursion (assoc-eq fn (strip-cdrs (cdr ev))))
      (verify-termination-boot-strap
       (cdr (cltl-def-from-name fn wrld)))
      (otherwise nil))))
;; Temporarily renamed to avoid conflict with fn-ubody
(defun fn-ubody1 (fn fn-body wrld ev)

; Return a body of fn, preferably an untranslated body, else an unnormalized
; body.  Fn-body may be nil; otherwise it is an unnormalized body of fn in
; wrld, (body fn nil wrld).  Ev may be nil; otherwise it the value of (get-def
; fn wrld nil).

  (or (car (last (get-def fn wrld ev)))
      fn-body
      (body fn nil wrld)))

(logic)

;; Temporary utility fns from make-axe-rules.lisp but generalized to untranslated-termp
;;  -- should be in in utilities dir
(defines flatten-conj/s
(define flatten-conj ((hyp untranslated-termp))
  ;:returns (conjuncts untranslated-term-listp)
  (if (and hyp (symbolp hyp))
      (list hyp)
    (if (atom hyp)
        ()
      (if (and (eq 'if (car hyp))       ;(if x y nil) => (and x y)
               (equal *nil* (fourth hyp)))
          (append (flatten-conj (second hyp))
                  (flatten-conj (third hyp)))
        (if (eq 'and (car hyp))
            (flatten-conjuncts (cdr hyp))
          (list hyp))))))
(define flatten-conjuncts ((conjuncts untranslated-term-listp))
  (if (endp conjuncts)
      ()
    (append (flatten-conj (car conjuncts))
            (flatten-conjuncts (cdr conjuncts)))))
) ; flatten-conj/s

(defund rule-hyps-and-conc (theorem-body rule-symbol)
  (declare (xargs :guard (untranslated-termp theorem-body)
                  :mode :program))
  (if (not (consp theorem-body))
      (mv (er hard? 'rule-hyps-and-conc "Unexpected form, ~x0, of a theorem for ~x1"
              theorem-body rule-symbol)
          nil)
    (case-match theorem-body
      (('implies lhs rhs)
       (b* (((mv r-hyps head) (rule-hyps-and-conc rhs rule-symbol)))
         (mv (append (flatten-conj lhs) r-hyps)
             head)))
      (('let binds bod)
       (rule-hyps-and-conc (sublis (doublets-to-alist binds) bod) rule-symbol))
      ((('lambda (v) bod) arg)
       (rule-hyps-and-conc (sublis `((,v . ,arg)) bod) rule-symbol))
      (& (mv nil                     ;no hyps
             theorem-body)))))

(defund implies-term? (tm)
  (case-match tm
    (('implies & &) t)
    (& nil)))

;; TODO: Make aware of structure of classes
(defun classes-subst (classes subst)
  (if (consp classes)
      (cons (classes-subst (car classes) subst)
            (classes-subst (cdr classes) subst))
    (let ((new (lookup-eq classes subst)))
      (or new classes))))

(deffilter filter-assoc (syms subst) (assoc syms subst)
  :fixed subst)

(defforall variable-listp (l) (variablep l) :true-listp t :guard t)

(deffilter remove-keys-from-alist (al keys) (not (member-equal (car al) keys))
  :fixed keys
  :guard (and (alistp al)
              (true-listp keys)))

(define remove-world-triples-before ((names symbol-listp) (world plist-worldp))
  :guard (acl2::logical-name-listp names world)
  ;; returns PLIST-WORLDP
  :mode :program
  (if (endp world)
      (raise "Unexpected: world has no event tuples for ~x0." names)
    (let ((eventup (car world)))
      (if (and (member (acl2::access-event-tuple-type eventup) '(defun defaxiom defthm))
               (member (acl2::access-event-tuple-namex eventup) names))
          world                                              ; found, done
        (remove-world-triples-before names (cdr world))))))

(define return-events-until ((world plist-worldp) (names symbol-listp))
  :guard (acl2::logical-name-listp names world)
  ;; returns PLIST-WORLDP
  :mode :program
  (if (endp world)
      (prog2$ (raise "Unexpected: world has no event tuples for ~x0." names)
              (mv nil nil))
    (let ((eventup (car world)))
      (if (and (member (acl2::access-event-tuple-type eventup) '(defun defaxiom defthm))
               (member (acl2::access-event-tuple-namex eventup) names))
          (mv (list (car world)) (cdr world))      ; found, done
        (b* (((mv good-eventups rest-eventups)
              (return-events-until (cdr world) names)))
          (mv (cons (car world) good-eventups)
              rest-eventups))))))

(define event-tuples-between-pairs ((event-regions symbol-alistp) (eventups plist-worldp))
  :mode :program
  (if (endp event-regions)
      eventups
    (let ((r-eventups (remove-world-triples-before (list (caar event-regions)) eventups)))
      (if (endp (cdr event-regions))
          r-eventups
        (b* (((mv good-eventups rest-eventups)
              (return-events-until r-eventups (list (cdar event-regions)))))
          (append good-eventups
                  (event-tuples-between-pairs (cdr event-regions) rest-eventups)))))))

;; Remove troublesome __function__ binding!
(define clean-body (body)
  :mode :program
  (case-match body
    (('let (('__function__ &))
       ('declare &)
       real-body)
     real-body)
    ;; Temporarily removed until generalize-to-lambda put in community books
    ;; ((('lambda formals body) . actuals)
    ;;  (apt::generalize-to-lambda formals actuals body))
    (& body)))


;; Support fns

(defun iso-info-elt-p (iso-info)
  (declare (xargs :guard t))
  (and (symbol-listp iso-info)
       (> (len iso-info) 4)))

(define iso-info-iso-name ((iso-info defmapping-infop))
  (let ((iso-rec (acl2::defmapping-info->call$ iso-info)))
    (case-match iso-rec
      (('defiso iso-name . &)
       iso-name))))

(define iso-info-old ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->doma iso-info))

(define iso-info-new ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->domb iso-info))

(define iso-info-pred ((iso-info defmapping-infop)
                       (new-p booleanp))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (if new-p
      (iso-info-new iso-info)
    (iso-info-old iso-info)))

(define iso-info-new-to-old ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->beta iso-info))

(define iso-info-old-to-new ((iso-info defmapping-infop))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (acl2::defmapping-info->alpha iso-info))

(define iso-info-convert-fn ((iso-info defmapping-infop)
                             (new-to-old-p booleanp))
  :returns (pred-name pseudo-termfnp :hyp :guard)
  (if new-to-old-p
      (iso-info-new-to-old iso-info)
    (iso-info-old-to-new iso-info)))

(define iso-info-alist-p (iso-infos)
  :guard t
  (or (null iso-infos)
      (and (consp iso-infos)
           (consp (first iso-infos))
           (symbolp (caar iso-infos))
           (defmapping-infop (cdar iso-infos))
           (iso-info-alist-p (rest iso-infos))))
///
(defthm true-listp-iso-info-alist-p
  (implies (iso-info-alist-p l)
           (true-listp l))
  :rule-classes (:forward-chaining))
(defthm iso-info-alist-p-car
  (implies (and (iso-info-alist-p iso-infos)
                (consp iso-infos))
           (consp (car iso-infos))))
(defthm iso-info-alist-p-caar
  (implies (and (iso-info-alist-p iso-infos)
                (consp iso-infos))
           (symbolp (caar iso-infos))))
(defthm iso-info-alist-p-cdar
  (implies (and (iso-info-alist-p iso-infos)
                (consp iso-infos))
           (defmapping-infop (cdar iso-infos))))
(defthm iso-info-alist-p-cdr
  (implies (iso-info-alist-p iso-infos)
           (iso-info-alist-p (cdr iso-infos))))
(defthm iso-info-alist-p-alistp
  (implies (iso-info-alist-p l)
           (alistp l)))
(defthm iso-info-alist-p-append
  (implies (and (iso-info-alist-p iso-infos)
                (symbolp s)
                (defmapping-infop o))
           (iso-info-alist-p (append iso-infos (list (cons s o))))))
) ; iso-info-alist-p

(define renaming-from-iso-infos ((iso-infos iso-info-alist-p))
  :returns (subst alistp)
  :verify-guards nil
  (if (endp iso-infos)
      ()
    (acons (iso-info-old (cdar iso-infos))
           (iso-info-new (cdar iso-infos))
           (renaming-from-iso-infos (cdr iso-infos)))))

(verify-guards renaming-from-iso-infos
  :hints (("Goal" :in-theory (enable iso-info-alist-p))))

(define iso-convert-theorems ((iso-infos iso-info-alist-p))
  ;:returns (thms symbol-listp)
  :mode :program
  (if (endp iso-infos)
      ()
    (b* (((defmapping-info iso) (cdar iso-infos))
         (r-thms (iso-convert-theorems (rest iso-infos))))
      (list* iso.alpha-image
             iso.beta-image
             iso.beta-of-alpha
             iso.alpha-of-beta
             iso.alpha-injective
             iso.beta-injective
             (if iso.alpha-guard
                 (list* iso.alpha-guard iso.beta-guard r-thms)
               r-thms)))))

(define lookup-iso-info ((f symbolp) (iso-infos iso-info-alist-p))
  (cdr (assoc f iso-infos))
///
(defthm defmapping-infop-lookup-iso-info
  (implies (and (iso-info-alist-p iso-infos)
                (lookup-iso-info f iso-infos))
           (defmapping-infop (lookup-iso-info f iso-infos))))
)

(define lookup-osi-info ((f symbolp) (iso-infos iso-info-alist-p))
  (if (atom iso-infos)
      nil
    (if (equal f (iso-info-new (cdar iso-infos)))
        (cdar iso-infos)
      (lookup-osi-info f (rest iso-infos))))
///
(defthm defmapping-infop-lookup-osi-info
  (implies (and (iso-info-alist-p iso-infos)
                (lookup-osi-info f iso-infos))
           (defmapping-infop (lookup-osi-info f iso-infos))))
)

(define source-of-iso-p ((f symbolp) (iso-infos iso-info-alist-p))
  (assoc f iso-infos))

(define target-of-iso-p ((f symbolp) (iso-infos iso-info-alist-p))
  (and (consp iso-infos)
       (or (equal f (iso-info-new (cdar iso-infos)))
           (target-of-iso-p f (rest iso-infos)))))

(define iso-info-f-pred ((f symbolp) (iso-infos iso-info-alist-p) (new-p booleanp))
  (let ((iso-info (lookup-iso-info f iso-infos)))
    (if iso-info
        (if new-p
            (iso-info-new iso-info)
          (iso-info-old iso-info))
      (raise "Shouldn't happen! ~x0 not in~%~x1" f iso-infos))))

;; Wraps tm in iso (osi) unless tm is a call to osi (iso) then it just returns the unwrapped tm
(define iso-info-convert-term ((type-pred symbolp)
                               (tm untranslated-termp)
                               (iso-infos iso-info-alist-p)
                               (new-to-old-p booleanp))
  (if (eq type-pred 'booleanp)
      tm
    (let ((iso-info (lookup-iso-info type-pred iso-infos)))
      (if iso-info
          (case-match tm
            ((f arg1)
             (if (equal f (iso-info-convert-fn iso-info (not new-to-old-p)))
                 arg1
               (list (iso-info-convert-fn iso-info new-to-old-p) tm)))
            (& (list (iso-info-convert-fn iso-info new-to-old-p) tm)))
        ;; (raise "Shouldn't happen! ~x0~%~x1not in ~%~x2" tm type-pred iso-infos)
        tm))))

(define map-iso-domb ((iso-infos iso-info-alist-p))
  ;:returns (fns symbol-listp)
  (if (atom iso-infos)
      ()
    (cons (iso-info-new (cdar iso-infos))
          (map-iso-domb (rest iso-infos)))))

(define valid-iso-domain-p ((ty symbolp) (iso-infos iso-info-alist-p))
  (or (symbol-name-equal ty "*")
      (source-of-iso-p ty iso-infos)))

(define valid-iso-domain-list-p ((tys symbol-listp) (iso-infos iso-info-alist-p))
  (or (endp tys)
      (and (valid-iso-domain-p (first tys) iso-infos)
           (valid-iso-domain-list-p (rest tys) iso-infos))))

(define find-iso-bindings ((hyps pseudo-term-listp) (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp hyps)
      ()
    (let ((r-bindings (find-iso-bindings (rest hyps) iso-infos))
          (hyp (first hyps)))
      (case-match hyp
        ((p v)
         (if (and (symbolp p)
                  (variablep v))
             (let ((p-info (lookup-iso-info p iso-infos)))
               (if p-info
                   (let ((iso-p-to-p (iso-info-new-to-old p-info)))
                     (cons (list v `(,iso-p-to-p ,v) )
                           r-bindings))
                 r-bindings))
           r-bindings))
        (& r-bindings)))))

(define find-osi-bindings ((hyps pseudo-term-listp) (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp hyps)
      ()
    (let ((r-bindings (find-osi-bindings (rest hyps) iso-infos))
          (hyp (first hyps)))
      (case-match hyp
        ((p v)
         (if (and (symbolp p)
                  (variablep v))
             (let ((p-info (lookup-osi-info p iso-infos)))
               (if p-info
                   (let ((osi-p-to-p (iso-info-new-to-old p-info)))
                     (cons (list v `(,osi-p-to-p ,v) )
                           r-bindings))
                 r-bindings))
           r-bindings))
        (& r-bindings)))))

(define variable-osi-subst ((var-ty-alist symbol-alistp) (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp var-ty-alist)
      ()
    (let* ((r-bindings (variable-osi-subst (rest var-ty-alist) iso-infos))
           (ty-pr (first var-ty-alist))
           (v (car ty-pr))
           (p-info (lookup-iso-info (cdr ty-pr) iso-infos)))
      (if p-info
          (let ((osi-p-to-p (iso-info-new-to-old p-info)))
            (cons (list v `(,osi-p-to-p ,v) )
                  r-bindings))
        r-bindings))))

(define arg-domain-for-var ((formal variablep)
                            (guards pseudo-term-listp)
                            (iso-infos iso-info-alist-p))
  :returns (ty symbolp :hyp :guard)
  (if (endp guards)
      '*
    (let* ((guard1 (first guards))
           (ty (case-match guard1
                 ((p formal1)
                  (and (symbolp p)
                       (equal formal1 formal)
                       (lookup-iso-info p iso-infos)
                       p)))))
      (or ty (arg-domain-for-var formal (rest guards) iso-infos)))))

(define arg-signature ((formals variable-listp)
                       (guards pseudo-term-listp)
                       (iso-infos iso-info-alist-p))
  (if (not (consp formals))
      ()
    (cons (arg-domain-for-var (first formals) guards iso-infos)
          (arg-signature (rest formals) guards iso-infos))))

;; substitutes all occurrences of pat by repl in str
(define string-subst ((str stringp) (pat stringp) (repl stringp))
  ;:measure (length str)
  ;:returns (s stringp :hyp :guard)
  :mode :program
  (let ((pos-i (search pat str)))
    (if (or (null pos-i)
            (equal str ""))
        str
      (concatenate 'string (subseq str 0 pos-i)
                   repl
                   (string-subst (subseq str (+ pos-i (length pat))
                                         (length str))
                                 pat repl)))))

(define string-subst-remove-p ((str stringp) (pat stringp) (repl stringp))
  :mode :program
  (if (and (search "-P" pat :start2 (- (length pat) 2))
           (search "-P" repl :start2 (- (length repl) 2)))
      (string-subst str
                    (subseq pat 0 (- (length pat) 2))
                    (subseq repl 0 (- (length repl) 2)))
    (string-subst str pat repl)))

;; substitute iso domain name if it occurs and the result is not already used,
;; else use the current transformation index for THM
(define new-name-maybe-using-isos ((fun symbolp)
                                   (iso-infos iso-info-alist-p)
                                   (thmp booleanp)
                                   (world plist-worldp))
  ;:returns (nm symbolp)
  :mode :program
  (if (endp iso-infos)
      (acl2::increment-name-suffix fun)
    (or (b* ((iso-info (cdar iso-infos))
             (new-fun-name
              (string-subst-remove-p (symbol-name fun)
                                     (symbol-name (acl2::defmapping-info->doma iso-info))
                                     (symbol-name (acl2::defmapping-info->domb iso-info))))
             ((when (equal new-fun-name (symbol-name fun)))
              nil)
             (new-sym (intern new-fun-name "ACL2")))
          new-sym)
        (new-name-maybe-using-isos fun (rest iso-infos) thmp world))))

(define dependent-on-iso-types-p ((sig-list symbol-listp) (iso-infos iso-info-alist-p))
  (and (consp sig-list)
       (or (lookup-iso-info (first sig-list) iso-infos)
           (dependent-on-iso-types-p (rest sig-list) iso-infos))))

(std::defaggregate propiso-info
                   ((iso-osi-ruleset-name symbolp)
                    (iso-ruleset-name symbolp)
                    (osi-ruleset-name symbolp)
                    (hints-map symbol-alistp)
                    (world plist-worldp)))

(define lookup-hints ((sym symbolp) (propiso-info propiso-info-p))
  (lookup-eq sym (propiso-info->hints-map propiso-info)))

(define iso-osi-thm-ruleset-form ((propiso-info propiso-info-p))
  `(expand-ruleset '(,(propiso-info->iso-osi-ruleset-name propiso-info)) world))

(define iso-thm-ruleset-form ((propiso-info propiso-info-p))
  `(expand-ruleset '(,(propiso-info->iso-ruleset-name propiso-info)) world))

(define osi-thm-ruleset-form ((propiso-info propiso-info-p))
  `(expand-ruleset '(,(propiso-info->osi-ruleset-name propiso-info)) world))

(define add-iso-osi-theorem-event (thms (propiso-info propiso-info-p))
  `(add-to-ruleset ,(propiso-info->iso-osi-ruleset-name propiso-info)
                   ',thms))

(define add-iso-theorem-event (thms (propiso-info propiso-info-p))
  `(add-to-ruleset ,(propiso-info->iso-ruleset-name propiso-info)
                   ',thms))

(define add-osi-theorem-event (thms (propiso-info propiso-info-p))
  `(add-to-ruleset ,(propiso-info->osi-ruleset-name propiso-info)
                   ',thms))

;; fn-info fns

(std::defaggregate fn-info-elt
                   ((source-fn symbolp)
                    (target-fn symbolp)
                    (iso-thm symbolp)
                    (osi-thm symbolp)
                    (arg-types symbol-listp)
                    (result-types symbol-listp)))

(define merge-fn-info-elt-iso-fn-type (fn-info? (fun symbolp) (fun1 symbolp) arg-sig ret-sig)
  :mode :program
  (if (null fn-info?)
      (fn-info-elt fun fun1 nil nil arg-sig ret-sig)
    (change-fn-info-elt fn-info?
                          :target-fn fun1
                          :arg-types arg-sig
                          :result-types ret-sig)))

(defforall fn-infos-list-p (el) (fn-info-elt-p el)
  :guard t
  :true-listp t)

(deffilter delete-fn-infos-for-fun (fn-infos fun)
  (not (equal fun (fn-info-elt->source-fn fn-infos)))
  :fixed fun)

(defun source-fns (fn-infos)
  (if (endp fn-infos)
      ()
    (let ((fn (fn-info-elt->source-fn (car fn-infos)))
          (r-val (source-fns (rest fn-infos))))
      (if (null fn)
          r-val
        (cons fn  r-val)))))
(defun target-fns (fn-infos)
  (if (endp fn-infos)
      ()
    (let ((fn (fn-info-elt->target-fn (car fn-infos)))
          (r-val (target-fns (rest fn-infos))))
      (if (null fn)
          r-val
        (cons fn  r-val)))))
(defun iso-thms (fn-infos)
  (if (endp fn-infos)
      ()
    (let ((thm (fn-info-elt->iso-thm (car fn-infos)))
          (r-val (iso-thms (rest fn-infos))))
      (if (null thm)
          r-val
        (cons thm  r-val)))))
(defun osi-thms (fn-infos)
  (if (endp fn-infos)
      ()
    (let ((thm (fn-info-elt->osi-thm (car fn-infos)))
          (r-val (osi-thms (rest fn-infos))))
      (if (null thm)
          r-val
        (cons thm  r-val)))))


(deffilter restrict-fn-infos-list (refd-funs fn-infos)
  (or (member (fn-info-elt->source-fn fn-infos) refd-funs)
      (member (fn-info-elt->target-fn fn-infos) refd-funs))
  :fixed refd-funs)

;; Duplicate of one in simplify-defun-impl.lisp
(defun remove-nils (lst)
  (cond ((endp lst) nil)
        ((null (car lst))
         (remove-nils (cdr lst)))
        (t
         (cons (car lst)
               (remove-nils (cdr lst))))))

(define lookup-fn-info-elt ((src-fn symbolp) (fn-infos fn-infos-list-p))
  :returns (elt (or (null elt)
                    (fn-info-elt-p elt))
                :hyp (fn-infos-list-p fn-infos))
  (if (endp fn-infos)
      nil
    (if (equal src-fn (fn-info-elt->source-fn (first fn-infos)))
        (first fn-infos)
      (lookup-fn-info-elt src-fn (rest fn-infos)))))

(define add-fn-info-iso-fn-type ((fun symbolp)
                                 (fun1 symbolp)
                                 arg-sig
                                 ret-sig
                                 (fn-infos fn-infos-list-p))
  :mode :program
  (let ((fn-info (lookup-fn-info-elt fun fn-infos))
        (fn-infos (delete-fn-infos-for-fun fn-infos fun)))
    (cons (merge-fn-info-elt-iso-fn-type fn-info fun fun1 arg-sig ret-sig)
          fn-infos)))

(define add-fn-info-iso-thms ((fun symbolp)
                              (fun1-is-iso-fun symbolp)
                              (fun-is-iso-fun1 symbolp)
                              (fn-infos fn-infos-list-p))
  :mode :program
  (let ((fn-info (lookup-fn-info-elt fun fn-infos))
        (fn-infos (delete-fn-infos-for-fun fn-infos fun)))
    (cons (change-fn-info-elt fn-info
                              :iso-thm fun1-is-iso-fun
                              :osi-thm fun-is-iso-fun1)
          fn-infos)))

(define lookup-result-types ((f symbolp) (fn-infos fn-infos-list-p))
  :mode :program
  (let ((fn-info (lookup-fn-info-elt f fn-infos)))
    (and fn-info (fn-info-elt->result-types fn-info))))

(define lookup-arg-types ((f symbolp) (fn-infos fn-infos-list-p))
  :mode :program
  (let ((fn-info (lookup-fn-info-elt f fn-infos)))
    (and fn-info (fn-info-elt->arg-types fn-info))))

(define type-theorem-p (thm)
  :returns (b booleanp)
  :hints (("Goal" :in-theory (enable acl2-count)))
  (case-match thm
    (('implies & head)
     (type-theorem-p head))
    ((('lambda (x) (p x))
      bod)
     (declare (ignorable x))
     (type-theorem-p `(,p ,bod)))
    ((p &)
     (symbolp p))))

(define iso-type-theorem (head (fn-infos fn-infos-list-p) (iso-infos iso-info-alist-p))
  (case-match head
    ((('lambda (x) (p x))
      bod)
     (declare (ignorable x))
     (iso-type-theorem `(,p ,bod) fn-infos iso-infos))
    ((p (f . &))
     (if (and (symbolp p)
              (symbolp f)
              (or (eq p 'booleanp)
                  (source-of-iso-p p iso-infos)
                  (lookup-fn-info-elt p fn-infos) ; ???
                  ))
         (mv f p)
       (mv nil nil)))
    (& (mv nil nil))))

(define osi-thms-for-source-fns ((src-fns symbol-listp) (fn-infos fn-infos-list-p))
  :mode :program
  (if (endp src-fns)
      ()
    (let ((fn-info (lookup-fn-info-elt (first src-fns) fn-infos))
          (r-val (osi-thms-for-source-fns (rest src-fns) fn-infos)))
      (if (null fn-info)            ; shouldn't happen!?
          r-val
        (cons (fn-info-elt->osi-thm fn-info)
              r-val)))))

(define renaming-from-fn-infos ((fn-infos fn-infos-list-p))
  ;:returns (subst symbol-alistp)
  (if (endp fn-infos)
      ()
    (acons (fn-info-elt->source-fn (car fn-infos))
           (fn-info-elt->target-fn (car fn-infos))
           (renaming-from-fn-infos (rest fn-infos)))))

(define theorem-names (thms)
  :returns (l symbol-listp)
  (if (atom thms)
      ()
    (cons (and (true-listp (car thms))
               (symbolp (second (car thms)))
               (second (car thms)))
          (theorem-names (cdr thms)))))

(defines variable-types/list/binds
(define variable-types ((term untranslated-termp)
                        (fn-infos fn-infos-list-p)
                        (iso-infos iso-info-alist-p)
                        (var-ty-alist symbol-alistp))
  :mode :program
  (if (atom term)
      var-ty-alist
    (case-match term
      (('cond (p e1) . r-cases)
       (variable-types `(cond . ,r-cases) fn-infos iso-infos
                       (variable-types e1 fn-infos iso-infos
                                       (variable-types p fn-infos iso-infos var-ty-alist))))
      ((('lambda vs . es) . args)
       (remove-keys-from-alist
        (variable-types (car (last es)) fn-infos iso-infos
                        (variable-types-list args nil fn-infos iso-infos var-ty-alist))
                               vs))
      (('let binds . es)
       (remove-keys-from-alist
        (variable-types (car (last es)) fn-infos iso-infos
                        (variable-types-binds binds fn-infos iso-infos var-ty-alist))
                               (alist-keys binds)))
      (('let* binds . es)
       (remove-keys-from-alist
        (variable-types (car (last es)) fn-infos iso-infos
                        (variable-types-binds binds fn-infos iso-infos var-ty-alist))
                               (alist-keys binds)))
      (('b* binds . es)
       ;; TODO: remove-keys-from-alist variables bound in b*
       (variable-types (car (last es))
                       fn-infos iso-infos
                       (variable-types-binds binds fn-infos iso-infos var-ty-alist))) ; todo handle more cases
      ((f . args)
       (let ((fn-info (lookup-fn-info-elt f fn-infos))
             (iso-info (lookup-iso-info f iso-infos)))
         (variable-types-list args (if iso-info
                                       (list f)
                                     (and fn-info (fn-info-elt->arg-types fn-info)))
                              fn-infos iso-infos var-ty-alist)))
      (& var-ty-alist))))
(define variable-type ((tm untranslated-termp)
                       (type symbolp)
                       (var-ty-alist symbol-alistp))
  (case-match tm
    (('force f-tm)
     (variable-type f-tm type var-ty-alist))
    (('cons & cdr-tm)                   ; what about car? Maybe typed elsewhere
     (variable-type cdr-tm type var-ty-alist))
    (& (if (and (symbolp tm)
                (not (null tm))
                (not (or (member type '(nil booleanp))
                         (symbol-name-equal type "*")))
                (not (assoc-eq tm var-ty-alist))) ; TODO: Check for best type?
           (acons tm type var-ty-alist)
         var-ty-alist))))
(define variable-types-list ((tms untranslated-term-listp)
                             (types symbol-alistp)
                             (fn-infos fn-infos-list-p)
                             (iso-infos iso-info-alist-p)
                             (var-ty-alist symbol-alistp))
  :mode :program
  (if (endp tms)
      var-ty-alist
    (let* ((var-ty-alist (variable-type (car tms) (car types) var-ty-alist)))
      (variable-types-list (cdr tms) (cdr types) fn-infos iso-infos
                           (variable-types (car tms) fn-infos iso-infos var-ty-alist)))))
(define variable-types-binds (tms
                              (fn-infos fn-infos-list-p)
                              (iso-infos iso-info-alist-p)
                              (var-ty-alist symbol-alistp))
  :mode :program
  (if (endp tms)
      var-ty-alist
    (variable-types-binds (cdr tms)
                          fn-infos iso-infos
                          (variable-types (cadar tms) fn-infos iso-infos var-ty-alist))))
) ; variable-types/list/binds

(define incorporate-iso-infos ((iso-infos iso-info-alist-p) (fn-infos fn-infos-list-p))
  :mode :program
  (if (endp iso-infos)
      fn-infos
    (cons (fn-info-elt (caar iso-infos)
                       (iso-info-new (cdar iso-infos))
                       nil  nil '(*) '(booleanp))
          (incorporate-iso-infos (rest iso-infos) fn-infos))))

(define incorporate-result-type-map ((result-type-map symbol-alistp) (fn-infos fn-infos-list-p))
  :mode :program
  (if (endp result-type-map)
      fn-infos
    (cons (fn-info-elt (caar result-type-map) nil nil nil nil (cadar result-type-map))
          (incorporate-result-type-map (rest result-type-map) fn-infos))))

(define result-types-from-theorems ((eventups acl2::pseudo-event-landmark-listp)
                                    (fn-infos fn-infos-list-p)
                                    (iso-infos iso-info-alist-p)
                                    (typing-thms symbol-listp)
                                    (world plist-worldp))
    :mode :program
    (if (endp eventups)
        (mv fn-infos typing-thms)
      ;; process event tuple according to type:
      (let ((eventup (car eventups)))
        (b* (((mv fn-infos typing-thms)
               (case (acl2::access-event-tuple-type eventup)
                 (defun (mv (let ((fun (acl2::access-event-tuple-namex eventup)))
                              (if (lookup-fn-info-elt fun fn-infos)
                                  fn-infos
                                (cons (fn-info-elt fun nil nil nil nil '(*))
                                      fn-infos)))
                            typing-thms))
                 ((defaxiom defthm)
                  (b* ((thm (acl2::access-event-tuple-namex eventup))
                       (formula (formula thm nil world))
                       ((mv - head) (rule-hyps-and-conc formula thm))
                       ((mv fun p) (iso-type-theorem head fn-infos iso-infos))
                       (old-fn-info (and fun (lookup-fn-info-elt fun fn-infos)))
                       (old-result-types (fn-info-elt->result-types old-fn-info)))
                    (mv (if old-fn-info
                            (cons (if (case-match old-result-types
                                        (((quote~ *)) t) ; temporary
                                        ((prev-type)
                                         (and (not (source-of-iso-p prev-type iso-infos))
                                              (source-of-iso-p p iso-infos)))
                                        (& nil))
                                      (change-fn-info-elt old-fn-info
                                                          :result-types (list p))
                                    old-fn-info)
                                  (delete-fn-infos-for-fun fn-infos fun))
                          fn-infos)
                        (if fun
                            (cons thm typing-thms)
                          typing-thms))))
                 (otherwise (mv fn-infos typing-thms)))))
          (result-types-from-theorems (cdr eventups) fn-infos iso-infos typing-thms world)))))

;; TODO: fix so that result types of nested mvs can be handled
(define result-signature-aux ((term pseudo-termp)
                              (fn-infos fn-infos-list-p)
                              (arg-ty-alist symbol-alistp))
  :mode :program
  (if (atom term)
      (cdr (assoc term arg-ty-alist))
    (case-match term
      (('if & e1 e2)
       (or (result-signature-aux e1 fn-infos arg-ty-alist)
           (result-signature-aux e2 fn-infos arg-ty-alist)))
      (('cond (& e1) . r-cases)
       (or (result-signature-aux e1 fn-infos arg-ty-alist)
           (result-signature-aux `(cond . ,r-cases) fn-infos arg-ty-alist)))
      ((('lambda vs . es) . &)
       (result-signature-aux (car (last es))
                             fn-infos (remove-keys-from-alist arg-ty-alist vs)))
      (('let binds . es)
       (result-signature-aux (car (last es))
                             fn-infos
                             (remove-keys-from-alist arg-ty-alist (strip-cars binds))))
      (('let* binds . es)
       (result-signature-aux (car (last es))
                             fn-infos
                             (remove-keys-from-alist arg-ty-alist (strip-cars binds))))
      (('b* & . es)
       ;; arg-ty-alist todo: find vars to remove. Conservatively remove all!
       (result-signature-aux (car (last es))
                             fn-infos nil))
      (('and . &) 'booleanp)
      (('or . tms) (result-signature-aux (car (last tms)) fn-infos arg-ty-alist))
      (('progn$ . tms) (result-signature-aux (car (last tms)) fn-infos arg-ty-alist))
      (('prog2$ & tm) (result-signature-aux tm fn-infos arg-ty-alist))
      (('mv x . tms)
       (let ((x-sig (result-signature-aux x fn-infos arg-ty-alist)))
         (append (if (null x-sig)
                     '(*)
                   (if (consp x-sig)
                       x-sig
                     (list x-sig)))
               (if tms
                   (result-signature-aux `(mv . ,tms) fn-infos arg-ty-alist)
                 ()))))
      ((f . &)
       (let ((fn-info (lookup-fn-info-elt f fn-infos)))
         (and fn-info (fn-info-elt->result-types fn-info))))
      (& nil))))

(define result-signature* ((term pseudo-termp)
                           (fn-infos fn-infos-list-p)
                           (arg-ty-alist symbol-alistp)
                           (r-sig0 symbol-listp))
  :mode :program
  (case-match r-sig0
    (((quote~ *))
     (let ((r-sig (result-signature-aux term fn-infos arg-ty-alist)))
       (if (null r-sig)
           '(*)
         (if (consp r-sig)
             r-sig
           (list r-sig)))))
    (& r-sig0)))

(define make-formal-conds ((formals symbol-listp)
                           (arg-sig symbol-listp)
                           (iso-infos iso-info-alist-p)
                           (new-to-old-p booleanp))
  ;:returns (conds pseudo-term-listp)
  (if (or (endp formals)
          (endp arg-sig))
    ()
    (let ((rval (make-formal-conds (rest formals) (rest arg-sig) iso-infos new-to-old-p))
          (arg-sig1 (first arg-sig))
          (formal1 (first formals)))
      (if (symbol-name-equal arg-sig1 "*")
          rval
        (let ((pred (iso-info-f-pred arg-sig1 iso-infos new-to-old-p)))
          (if pred
              (cons `(force (,pred ,formal1)) rval)
            rval))))))

(define make-converted-args
  ((f symbolp)
   (args untranslated-term-listp)
   (arg-sig symbol-listp)
   (iso-infos iso-info-alist-p)
   (new-to-old-p booleanp))
  ;:returns (conv-args untranslated-term-listp)
  (if (endp args)
    ()
    (if (endp arg-sig)
        (raise "Missing signature for (~x0 . ~x1)" f args )
      (let* ((arg-sig1 (first arg-sig))
             (formal1 (first args))
             (iso-info (lookup-iso-info arg-sig1 iso-infos))
             (conv-arg1 (if (null iso-info)
                            formal1
                          (iso-info-convert-term arg-sig1 formal1 iso-infos new-to-old-p))))
        (cons conv-arg1
              (make-converted-args f (rest args) (rest arg-sig) iso-infos new-to-old-p))))))

(defconst *return-var-names* '(r0 r1 r2 r3 r4 r5 r6 r7 r8 r9))
(define get-n-return-var-names ((n natp))
  :returns (vars symbol-listp)
  (if (< n 10)
      (take n *return-var-names*)
    (raise "~x0 is more than 10 return values" n)))

(define make-mv-let-conversion
  (body (ret-sig symbol-listp) (iso-infos iso-info-alist-p) (new-to-old-p booleanp))
  :mode :program
  ;:returns (fm pseudo-termp)
  (let* ((rvars (get-n-return-var-names (len ret-sig)))
         (conv-rvars (make-converted-args 'mv-let rvars ret-sig iso-infos new-to-old-p)))
    `(mv-let ,rvars
         ,body
       (mv ,@conv-rvars))))

(define make-impl-nice ((hyps true-listp) head)
  (if (null hyps)
      head
    (let ((condn (acl2::make-and-nice hyps)))
      (if (equal condn 't)
          head
        `(implies ,condn ,head)))))

(define iso-pred-term? ((tm untranslated-termp)
                        (iso-infos iso-info-alist-p)
                        (new-to-old-p booleanp))
  (and (consp tm)
       (symbolp (car tm))
       (if new-to-old-p
           (lookup-osi-info (car tm) iso-infos)
         (lookup-iso-info (car tm) iso-infos))))

(define filter-iso-pred-terms ((pred-tms untranslated-term-listp)
                               (iso-infos iso-info-alist-p)
                               (new-to-old-p booleanp))
  :returns (new-pred-tms untranslated-term-listp
                         :hyp (untranslated-term-listp pred-tms))
  (if (endp pred-tms)
      ()
    (if (iso-pred-term? (car pred-tms) iso-infos new-to-old-p)
        (cons `(force ,(car pred-tms))
              (filter-iso-pred-terms (cdr pred-tms)
                                      iso-infos new-to-old-p))
      (filter-iso-pred-terms (cdr pred-tms)
                              iso-infos new-to-old-p))))

(define iso-theorem-for-fns ((fun symbolp)
                             (fun1 symbolp)
                             (formals symbol-listp)
                             (guard-tms untranslated-term-listp)
                             (arg-sig symbol-listp)
                             (ret-sig symbol-listp)
                             (iso-infos iso-info-alist-p)
                             (new-to-old-p booleanp))
  :mode :program
  ;:returns (fm pseudo-termp)
  (let* ((hyps (make-formal-conds formals arg-sig iso-infos new-to-old-p))
         (iso-guard-tms (filter-iso-pred-terms guard-tms iso-infos new-to-old-p))
         (hyps (union-equal hyps iso-guard-tms))
         (fun1-args (make-converted-args fun formals arg-sig iso-infos new-to-old-p))
         (fn1-tm `(,fun1 ,@fun1-args))
         (rhs (case-match ret-sig
                (((quote~ *)) fn1-tm)
                (& (if (equal 1 (len ret-sig))
                       (iso-info-convert-term (first ret-sig) fn1-tm iso-infos (not new-to-old-p))
                     (make-mv-let-conversion fn1-tm ret-sig iso-infos (not new-to-old-p))))))
         (equality `(equal (,fun ,@formals)
                           ,rhs)))
    (make-impl-nice hyps equality)))

;; (f x y) --> (osi (f x (iso y))) if arg-sig (* iso-pred) and ret-sig (iso-pred) and new-to-old-p is nil
(define make-iso-osi-term ((fun symbolp)
                           (args symbol-listp)
                           (arg-sig symbol-listp)
                           (ret-sig symbol-listp)
                           (iso-infos iso-info-alist-p)
                           (new-to-old-p booleanp))
  :mode :program
  (let* ((fun-args (make-converted-args fun args arg-sig iso-infos new-to-old-p))
         (fn-tm `(,fun ,@fun-args))
         (conv-tm (case-match ret-sig
                    (((quote~ *)) fn-tm)
                    (& (if (equal 1 (len ret-sig))
                           (iso-info-convert-term (first ret-sig) fn-tm iso-infos (not new-to-old-p))
                         (make-mv-let-conversion fn-tm ret-sig iso-infos (not new-to-old-p)))))))
    conv-tm))

(defines add-iso-conversions/list/binds
(define add-iso-conversions ((tm untranslated-termp)
                             (fn-infos fn-infos-list-p)
                             (iso-infos iso-info-alist-p))
  :mode :program
  (case-match tm
    (('let binds bod)
     `(let ,(add-iso-conversions-binds binds fn-infos iso-infos)
        ,(add-iso-conversions bod fn-infos iso-infos)))
    (('let* binds bod)
     `(let* ,(add-iso-conversions-binds binds fn-infos iso-infos)
        ,(add-iso-conversions bod fn-infos iso-infos)))
    ((('lambda vars bod) . args)
     `((lambda ,vars ,(add-iso-conversions bod fn-infos iso-infos))
       ,@(add-iso-conversions-list args fn-infos iso-infos)))
    ((f . args)
     (let ((converted-args (add-iso-conversions-list args fn-infos iso-infos))
           (fn-info (lookup-fn-info-elt f fn-infos)))
       (if fn-info
           (make-iso-osi-term f converted-args
                              (fn-info-elt->arg-types fn-info)
                              (fn-info-elt->result-types fn-info)
                              iso-infos t)
         `(,f ,@converted-args))))
    (& tm)))                       ; TODO: add more cases
(define add-iso-conversions-list ((tms untranslated-term-listp)
                                  (fn-infos fn-infos-list-p)
                                  (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp tms)
      ()
    (cons (add-iso-conversions (car tms) fn-infos iso-infos)
          (add-iso-conversions-list (cdr tms) fn-infos iso-infos))))
(define add-iso-conversions-binds (tms (fn-infos fn-infos-list-p) (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp tms)
      ()
    (cons (list (caar tms) (add-iso-conversions (cadar tms) fn-infos iso-infos))
          (add-iso-conversions-binds (cdr tms) fn-infos iso-infos)))))

(defines add-iso-conversions-for-fun/list/binds
(define add-iso-conversions-for-fun (body-tm
                                     (fun symbolp)
                                     (arg-sig symbol-listp)
                                     (ret-sig symbol-listp)
                                     (iso-infos iso-info-alist-p))
  :mode :program
  (case-match body-tm
    ((!fun . args)
     (make-iso-osi-term fun args arg-sig ret-sig iso-infos t))
    (('let binds bod)
     `(let ,(add-iso-conversions-for-fun-binds binds fun arg-sig ret-sig iso-infos)
        ,(add-iso-conversions-for-fun bod fun arg-sig ret-sig iso-infos)))
    (('let* binds bod)
     `(let* ,(add-iso-conversions-for-fun-binds binds fun arg-sig ret-sig iso-infos)
        ,(add-iso-conversions-for-fun bod fun arg-sig ret-sig iso-infos)))
    ((('lambda vars bod) . args)
     `((lambda ,vars ,(add-iso-conversions-for-fun bod fun arg-sig ret-sig iso-infos))
       ,@(add-iso-conversions-for-fun-list args fun arg-sig ret-sig iso-infos)))
    ((f . args)
     `(,f ,@(add-iso-conversions-for-fun-list args fun arg-sig ret-sig iso-infos)))
    (& body-tm)))                       ; TODO: add more cases
(define add-iso-conversions-for-fun-list (tms
                                          (fun symbolp)
                                          (arg-sig symbol-listp)
                                          (ret-sig symbol-listp)
                                          (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp tms)
      ()
    (cons (add-iso-conversions-for-fun (car tms) fun arg-sig ret-sig iso-infos)
          (add-iso-conversions-for-fun-list (cdr tms) fun arg-sig ret-sig iso-infos))))
(define add-iso-conversions-for-fun-binds (tms
                                           (fun symbolp)
                                           (arg-sig symbol-listp)
                                           (ret-sig symbol-listp)
                                           (iso-infos iso-info-alist-p))
  :mode :program
  (if (endp tms)
      ()
    (cons (list (caar tms) (add-iso-conversions-for-fun (cadar tms) fun arg-sig ret-sig iso-infos))
          (add-iso-conversions-for-fun-binds (cdr tms) fun arg-sig ret-sig iso-infos)))))

(define binds-to-equals ((binds symbol-alistp))
  (if (endp binds)
      ()
    (cons `(equal ,@(car binds))
          (binds-to-equals (cdr binds)))))

;; Generate theorem for each branch of if-then-else
(define local-names ((local-thms true-listp))
  (if (endp local-thms)
      ()
    (let* ((thm (first local-thms))
           (thm-name (case-match thm
                       (('local ('skip-proofs (& thm-name . &)))
                        thm-name)
                       (('local ('remove-hyps (& thm-name . &) . &))
                        thm-name)
                       (('local (& thm-name . &))
                        thm-name))))
      (cons thm-name
            (local-names (rest local-thms))))))

(define support-thms-for-defun-aux (old-body-tm ; sub-term of function body
                                    (hyps true-listp) ; list of predicates that are true in context
                                    (n natp)
                                    (fun symbolp)
                                    (fun1 symbolp)
                                    head-tm
                                    (fn-renaming symbol-alistp)
                                    (fn-infos fn-infos-list-p)
                                    (iso-infos iso-info-alist-p)
                                    (propiso-info propiso-info-p))
                                        ;:returns (events true-list-listp)
  :mode :program
  (case-match old-body-tm
    (('if pred then-cl else-cl)
     (let ((pred (rename-fns-in-untranslated-term pred fn-renaming)))
       (append (support-thms-for-defun-aux then-cl (cons pred hyps)
                                           (+ n 1)
                                           fun fun1 head-tm fn-renaming fn-infos iso-infos propiso-info)
               (support-thms-for-defun-aux else-cl (cons `(not ,pred) hyps)
                                           (+ n 100)
                                           fun fun1 head-tm fn-renaming fn-infos iso-infos propiso-info))))
    (('let binds let-body)
     (let ((subst-let-body (sublis-var-untranslated-term (doublets-to-alist binds) let-body)))
       (support-thms-for-defun-aux subst-let-body hyps n fun fun1 head-tm fn-renaming fn-infos iso-infos propiso-info)))
    (('let* () let-body)
     (support-thms-for-defun-aux let-body hyps n fun fun1 head-tm fn-renaming fn-infos iso-infos propiso-info))
    (('let* ((v val) . r-binds) let-body)
     (let ((new-let* (sublis-var-untranslated-term (acons v val ())
                                                   `(let* ,r-binds ,let-body))))
       (support-thms-for-defun-aux new-let* hyps n fun fun1 head-tm fn-renaming fn-infos iso-infos propiso-info)))
    ;; ((mv . mvs))  ;; ??
    (& (b* ((thm-name (pack$ fun1 "--" n))
            (body-tm (rename-fns-in-untranslated-term old-body-tm fn-renaming))
            (body-tm (add-iso-conversions body-tm fn-infos iso-infos))
            (hyps (add-iso-conversions-list hyps fn-infos iso-infos))
            (thm-body (make-impl-nice hyps `(equal ,head-tm ,body-tm)))
            ;; (refd-funs (all-ffn-symbs (rename-fns-in-untranslated-term thm-body fn-renaming) nil))
            (user-hints (lookup-hints thm-name propiso-info))
            (skip-proofs-p (eq user-hints 'skip-proofs))
            (user-e/d (and (consp user-hints)
                           (member (car user-hints) '(enable disable e/d))))
            ((mv user-enable-runes user-disable-runes)
             (parse-enable-disable-e/d user-hints))
            (hints (if (and user-hints (not user-e/d))
                       user-hints
                     (enable-disable-runes-in-hints
                      `(("Goal" :in-theory (e/d* (,fun (:type-prescription ,fun)
                                                       ,(propiso-info->osi-ruleset-name propiso-info)
                                                       ,(propiso-info->iso-osi-ruleset-name propiso-info))
                                                 (,(propiso-info->iso-ruleset-name propiso-info)))
                         :do-not-induct t))
                      user-hints))))
         (if skip-proofs-p
             `((local (skip-proofs (defthmd ,thm-name
                                     ,thm-body))))
           (if nil  ;hyps
               `((local (remove-hyps (defthmd ,thm-name
                                       ,thm-body
                                       ,@(if hints `(:hints ,hints) ()))
                                     t)))
             `((local
                (defthmd ,thm-name
                  ,thm-body
                  ,@(if hints
                        `(:instructions
                          ((succeed (prove :hints ,hints))
                           ;; (when-not-proved (print "support: prove failed!"))
                           (succeed (bash ,@hints))
                           ;; (when-not-proved (print "support: bash failed!"))
                           (repeat
                            (bash ("Goal" :in-theory (e/d* (,(propiso-info->osi-ruleset-name propiso-info)
                                                            ,@user-enable-runes)
                                                           (,(propiso-info->iso-ruleset-name propiso-info)
                                                            ,@user-disable-runes)))))))
                      ()))))))))))

(define support-thms-for-defun (old-body-tm      ; sub-term of function body
                                (hyps true-listp) ; list of predicates that are true in context
                                (fun symbolp)
                                (fun1 symbolp)
                                (formals symbol-listp)
                                (ret-sig symbol-listp)
                                head-tm
                                (recursive booleanp)
                                (fn-renaming symbol-alistp)
                                (fn-infos fn-infos-list-p)
                                (iso-infos iso-info-alist-p)
                                (propiso-info propiso-info-p))
  ;; :returns (mv (thm-names symbol-listp)
  ;;              (events true-list-listp))
  :mode :program
  (let* ((local-thms (and recursive
                          (support-thms-for-defun-aux old-body-tm hyps 0 fun fun1 head-tm fn-renaming fn-infos iso-infos propiso-info)))
         (num-results (len ret-sig))
         (length-thm-name (and (> num-results 1)
                               (pack$ fun "--LEN")))
         (length-thm (and length-thm-name
                          `((defthm ,length-thm-name
                              (equal (len (,fun ,@formals))
                                     ,num-results)
                              :hints (("Goal" :in-theory (e/d (,fun) ((:executable-counterpart force)))))))))
         (mv-thm-names (nth num-results *list-mv-thms*)))
    (mv (and length-thm `(,length-thm-name ,@mv-thm-names))
        (local-names local-thms)
        (append length-thm local-thms))))

(defconst *unhandled-case* '*unhandled-case*)
(defconst *unknown-value* '*unknown-value*)

(defines merge-convert-exprs-for-and-n
(define merge-convert-exprs-for-and (exprs)
  (if (atom exprs)
      *unknown-value*
    (if (atom (cdr exprs))
        (car exprs)
      (merge-2-convert-exprs-for-and (car exprs) (merge-convert-exprs-for-and (cdr exprs))))))
(define merge-2-convert-exprs-for-and (e1 e2)
  (let* ((pr (list e1 e2)))
    (case-match pr
      ((('CONS c1a c2a)
        ('CONS c1b c2b))
       `(cons ,(merge-2-convert-exprs-for-and c1a c1b)
              ,(merge-2-convert-exprs-for-and c2a c2b)))
      ((!*unknown-value* e2)
       e2)
      ((e1 !*unknown-value*)
       e1)
      ((!*unhandled-case* e2)         ; These 2 cases require more thought
       e2)
      ((e1 !*unhandled-case*)
       e1)
      (& (if (equal e1 e2)
             e1
           *unhandled-case*)))))
)  ; merge-convert-exprs-for-and-n

(define merge-convert-exprs-for-or (t1 e1 e2)
  (if (or (equal e1 *unhandled-case*)
          (equal e2 *unhandled-case*))
      *unhandled-case*
    `(if ,t1 ,e1 ,e2)))

(define fill-in-unknowns-by-old (tm old-val-tm)
  (case-match tm
    (!*unknown-value* old-val-tm)
    (('CONS x y)
     `(cons ,(fill-in-unknowns-by-old x `(car ,old-val-tm))
            ,(fill-in-unknowns-by-old y `(cdr ,old-val-tm))))
    (('IF p x y)
     `(if ,p ,(fill-in-unknowns-by-old x old-val-tm)
        ,(fill-in-unknowns-by-old y old-val-tm)))
    (& tm)))

;;; Derived isomorphism functions
(defines convert-fn/s-for-new-iso-fn
(define convert-fn-for-new-iso-fn (old-body
                                   (pred-name symbolp)
                                   (formal variablep)
                                   (convert-fn-name symbolp)
                                   (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                   (iso-infos iso-info-alist-p))
  (case-match old-body
    (T formal)
    (('NULL !formal)
     'nil)
    (('NOT !formal)
     'nil)
    ((f !formal)
     (let ((iso-info (and (symbolp f)
                          (lookup-osi-info f iso-infos))))
       (if (not (null iso-info))
           `(,(iso-info-convert-fn iso-info new-to-old-p) ,formal)
         *unhandled-case*)))
    ((iso-p? ('CAR !formal))
     (let ((iso-info (and (symbolp iso-p?)
                          (lookup-osi-info iso-p? iso-infos))))
       (if (not (null iso-info))
           `(cons (,(iso-info-convert-fn iso-info new-to-old-p) (car ,formal))
                  ,*unknown-value*)
         *unhandled-case*)))
    ((iso-p? ('FIRST !formal))          ; same as CAR: keep consistent
     (let ((iso-info (and (symbolp iso-p?)
                          (lookup-osi-info iso-p? iso-infos))))
       (if (not (null iso-info))
           `(cons (,(iso-info-convert-fn iso-info new-to-old-p) (first ,formal))
                  ,*unknown-value*)
         *unhandled-case*)))
    ((iso-p? ('HEAD !formal))           ; same as CAR: keep consistent
     (let ((iso-info (and (symbolp iso-p?)
                          (lookup-osi-info iso-p? iso-infos))))
       (if (not (null iso-info))
           `(cons (,(iso-info-convert-fn iso-info new-to-old-p) (head ,formal))
                  ,*unknown-value*)
         *unhandled-case*)))
    ((iso-p? ('CAAR !formal))
     (let ((iso-info (and (symbolp iso-p?)
                          (lookup-osi-info iso-p? iso-infos))))
       (if (not (null iso-info))
           `(cons (cons (,(iso-info-convert-fn iso-info new-to-old-p) (caar ,formal))
                        ,*unknown-value*)
                  ,*unknown-value*)
         *unhandled-case*)))
    ((iso-p? ('CDAR !formal))
     (let ((iso-info (and (symbolp iso-p?)
                          (lookup-osi-info iso-p? iso-infos))))
       (if (not (null iso-info))
           `(cons (cons ,*unknown-value*
                        (,(iso-info-convert-fn iso-info new-to-old-p) (cdar ,formal)))
                  ,*unknown-value*)
         *unhandled-case*)))
    ((!pred-name ('CDR !formal))
     `(cons *unknown-value* (,convert-fn-name (cdr ,formal))))
    ((!pred-name ('REST !formal))
     `(cons *unknown-value* (,convert-fn-name (rest ,formal))))
    (('OR t1 t2)
     (merge-convert-exprs-for-or t1
                                 (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
                                 (convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos)))
    (('AND . r-tms)
     (merge-convert-exprs-for-and
      (convert-fns-for-new-iso-fn r-tms pred-name formal convert-fn-name new-to-old-p iso-infos)))
    (('IF t1 'T t2)
     (if (eq t2 'NIL)
         (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
       (merge-convert-exprs-for-or t1
                                   (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
                                   (convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos))))
    (('IF t1 t2 'NIL)                   ; TODO: check if this is sufficient for n-ary AND. E.g. ('IF t1 ('IF t2 t3 'NIL) 'NIL)
     (if (eq t2 'T)
         (convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
       (merge-convert-exprs-for-and
        (convert-fns-for-new-iso-fn (list t1 t2) pred-name formal convert-fn-name new-to-old-p iso-infos))))
    (('IF p t1 t2)
     `(if ,p
          ,(convert-fn-for-new-iso-fn t1 pred-name formal convert-fn-name new-to-old-p iso-infos)
        ,(convert-fn-for-new-iso-fn t2 pred-name formal convert-fn-name new-to-old-p iso-infos)))
    (& *unhandled-case*)))

(define convert-fns-for-new-iso-fn (old-body-tms
                                    (pred-name symbolp)
                                    (formal variablep)
                                    (convert-fn-name symbolp)
                                    (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                    (iso-infos iso-info-alist-p))
  (if (atom old-body-tms)
      *unhandled-case*                  ; shouldn't happen
    (if (atom (cdr old-body-tms))
        (list (convert-fn-for-new-iso-fn (car old-body-tms)
                                         pred-name formal convert-fn-name new-to-old-p iso-infos))
      (cons (convert-fn-for-new-iso-fn (car old-body-tms)
                                       pred-name formal convert-fn-name new-to-old-p iso-infos)
            (convert-fns-for-new-iso-fn (cdr old-body-tms)
                                        pred-name formal convert-fn-name new-to-old-p iso-infos)))))
) ; convert-fn/s-for-new-iso-fn

(define convert-fn-for-new-iso-fn0 (old-body
                                    (pred-name symbolp)
                                    (formal variablep)
                                    (convert-fn-name symbolp)
                                    (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                    (iso-infos iso-info-alist-p))
  (let ((raw-body (convert-fn-for-new-iso-fn old-body pred-name formal convert-fn-name new-to-old-p iso-infos)))
    (fill-in-unknowns-by-old raw-body formal)))

;; Returns type theorems for new conversion function based on the predicate that generated it
#|
Example: int10-map-p-->-int20-map-p
(define int20-map-p (m)
  (if (atom m)
      (null m)
    (and (consp (car m))
         (int20 (caar m))
         (int20 (cdar m))
         (int20-map-p (cdr m)))))
(defthm int10-map-p-->-int20-map-p-atom
  (implies (and (int10-map-p m) (atom p))
           (null (int10-map-p-->-int20-map-p m))))
(defthm int10-map-p-->-int20-map-p-not-atom
  (implies (and (int10-map-p m) (not (atom p)))
           (consp (int10-map-p-->-int20-map-p m))))
(defthm int10-map-p-->-int20-map-p-not-atom-caar
  (implies (and (int10-map-p m) (not (atom p)))
           (int20 (caar (int10-map-p-->-int20-map-p m)))))
(defthm int10-map-p-->-int20-map-p-not-atom-cdar
  (implies (and (int10-map-p m) (not (atom p)))
           (int20 (cdar (int10-map-p-->-int20-map-p m)))))
(defthm int10-map-p-->-int20-map-p-not-atom-cdr
  (implies (and (int10-map-p m) (not (atom p)))
           (int20 (cdar (int10-map-p-->-int20-map-p m)))))
|#

(define name-from-term (tm)
  :returns (tm symbolp)
  (if (symbolp tm)
      tm
    (if (consp tm)
        (name-from-term (car tm))
      'strange-term)))

(define implicit-theorems-for-new-iso (rhs-condns condn (thm-name symbolp) enable)
  (if (atom rhs-condns)
      ()
    (cons `(defthm ,(pack$ thm-name "--" (name-from-term (car rhs-condns)))
             (implies ,condn
                      ,(car rhs-condns))
             :hints (("Goal" :in-theory (enable ,enable))))
          (implicit-theorems-for-new-iso (cdr rhs-condns) condn thm-name enable))))

(defines term/s-with-subst-and-name
(define term-with-subst-and-name (tm (formal variablep)
                                     (convert-fn-name symbolp)
                                     (thm-name stringp))
  (if (equal tm formal)
      (mv `(,convert-fn-name ,formal)
          thm-name
          nil)
    (if (and (consp tm)
             (symbolp (car tm)))
        (mv-let (tms nm condns)
            (terms-with-subst-and-name (cdr tm) formal convert-fn-name
                                       (concatenate 'string thm-name "-"
                                                    (symbol-name (car tm))))
          (mv `(,(car tm) ,@tms)
              nm
              (if (member-eq (car tm) '(car first))
                  (cons `(consp ,@tms)
                        condns)
                condns)))
      (mv tm nil nil))))
(define terms-with-subst-and-name (tms (formal variablep)
                                       (convert-fn-name symbolp)
                                       (thm-name stringp))
  (if (atom tms)
      (mv nil nil nil)
    (b* (((mv car-tm car-nm car-condns)
          (term-with-subst-and-name (car tms) formal convert-fn-name thm-name))
         ((mv cdr-tms cdr-nm cdr-conds)
          (terms-with-subst-and-name (cdr tms) formal convert-fn-name thm-name))
         ((unless (and (true-listp car-condns) ; temporary heavy-hand
                       (true-listp cdr-conds)))
          (mv (cons car-tm cdr-tms)
              (if car-nm
                  car-nm
                cdr-nm)
              ())))
      (mv (cons car-tm cdr-tms)
          (if car-nm
              car-nm
            cdr-nm)
          (append car-condns cdr-conds)))))
)  ; term/s-with-subst-and-name


(defines type-theorems-for-new-iso-fn/-lst
(define type-theorems-for-new-iso-fn (old-body
                                      (formal variablep)
                                      (convert-fn-name symbolp)
                                      (renaming-pred symbolp) ; only non-nil if there it is a renaming predicate
                                      condns
                                      (thm-name stringp)
                                      (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                      (iso-infos iso-info-alist-p))
  (case-match old-body
    (('OR . &) ())  ; Not sure if this needs anything else
    (('AND . r-tms)
     (type-theorems-for-new-iso-fn-lst r-tms formal convert-fn-name renaming-pred condns
                                       thm-name new-to-old-p iso-infos))
    (('IF p t1 t2)
     (append (type-theorems-for-new-iso-fn t2 formal convert-fn-name renaming-pred
                                           (cons (negate-term p) condns)
                                           thm-name new-to-old-p iso-infos)
             (type-theorems-for-new-iso-fn t1 formal convert-fn-name renaming-pred (cons p condns)
                                           thm-name new-to-old-p iso-infos)))
    ((p . args)
     (if (symbolp p)
         (b* ((iso-info (lookup-osi-info p iso-infos))
              (new-p (if iso-info
                         (iso-info-pred iso-info new-to-old-p)
                       p))
              ((mv new-args thm-nm rhs-condns)
               (terms-with-subst-and-name args formal convert-fn-name thm-name))
              (condn `(and ,@(rev condns)))
              (enabled (or renaming-pred convert-fn-name))
              (thm-base-nm (if renaming-pred
                            (pack$ renaming-pred "-" convert-fn-name "-" new-p)
                          (pack$ convert-fn-name "-" new-p))))
           (list* `(defthm ,(pack$ thm-base-nm thm-nm)
                     (implies ,condn
                              (,new-p ,@new-args))
                     :hints (("Goal" :in-theory (enable ,enabled))))
                  (implicit-theorems-for-new-iso rhs-condns condn thm-base-nm enabled)))
       ()))
    (& ())))
(define type-theorems-for-new-iso-fn-lst (old-body-tms
                                          (formal variablep)
                                          (convert-fn-name symbolp)
                                          (renaming-pred symbolp) ; only non-nil if there it is a renaming predicate
                                          condns
                                          (thm-name stringp)
                                          (new-to-old-p booleanp) ; return convert from old to new, otherwise new to old
                                          (iso-infos iso-info-alist-p))
  (if (atom old-body-tms)
      ()
    (append (type-theorems-for-new-iso-fn-lst (cdr old-body-tms)
                                              formal convert-fn-name renaming-pred condns thm-name new-to-old-p iso-infos)
            (type-theorems-for-new-iso-fn (car old-body-tms)
                                          formal convert-fn-name renaming-pred condns thm-name new-to-old-p iso-infos))))
) ; type-theorems-for-new-iso-fn/-lst

(define find-definition-in-events ((fn symbolp) (events true-listp))
  (if (endp events)
      nil
    (let ((this-event (car events)))
      (case-match this-event
        (('defun !fn (v) & body)        ; Has to be unary with a single declare unless make-new-iso-pred-events changes
         (cons v body))
        (('encapsulate & . encap-events)
         (and (true-listp encap-events)
              (or (find-definition-in-events fn encap-events)
                  (find-definition-in-events fn (cdr events)))))
        (& (find-definition-in-events fn (cdr events)))))))

(define find-previous-iso-with-equivalent-definition ((convert-old-to-new-fn symbolp)
                                                      (convert-new-to-old-fn symbolp)
                                                      (formal symbolp)
                                                      convert-old-to-new-fn-body
                                                      (iso-infos iso-info-alist-p)
                                                      (events true-list-listp))
  :returns (mv (use-old-convert-fns-p booleanp)
               (ret-convert-old-to-new-fn symbolp :hyp (symbolp convert-old-to-new-fn))
               (ret-convert-new-to-old-fn symbolp :hyp (symbolp convert-new-to-old-fn)))
  (if (endp iso-infos)
      (mv nil convert-old-to-new-fn convert-new-to-old-fn)
    (b* ((iso (cdar iso-infos))
         (alpha (acl2::defmapping-info->alpha iso))
         (beta  (acl2::defmapping-info->beta  iso))
         ((unless (and (symbolp alpha)
                       (symbolp beta)))
          (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                        formal convert-old-to-new-fn-body
                                                        (cdr iso-infos) events))
         (found-def (find-definition-in-events alpha events))
         ((unless (and (consp found-def)
                       (symbolp (car found-def))))
          (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                        formal convert-old-to-new-fn-body
                                                        (cdr iso-infos) events))
         ((cons new-formal body) found-def))
      (if (equal convert-old-to-new-fn-body
                 (sublis (list (cons new-formal formal)
                               (cons alpha convert-old-to-new-fn))
                         body))
          (mv t
              (acl2::defmapping-info->alpha iso)
              (acl2::defmapping-info->beta iso))
        (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                      formal convert-old-to-new-fn-body
                                                      (cdr iso-infos) events)))))

;;; Try to reuse existing function either if body is just a fn call or iso fn defined in events
(define maybe-use-old-definitions ((convert-old-to-new-fn symbolp)
                                   (convert-new-to-old-fn symbolp)
                                   (formal symbolp)
                                   convert-old-to-new-fn-body
                                   convert-new-to-old-fn-body
                                   (iso-infos iso-info-alist-p)
                                   (events true-list-listp))
  :returns (mv (use-old-convert-fns-p booleanp)
               (existing-convert-old-to-new-fn symbolp :hyp (symbolp convert-old-to-new-fn))
               (existing-convert-new-to-old-fn symbolp :hyp (symbolp convert-new-to-old-fn)))
  (let ((bodies (list convert-old-to-new-fn-body convert-new-to-old-fn-body)))
    (case-match bodies
      (((f1 !formal) (f2 !formal))
       (if (and (symbolp f1) (symbolp f2))
           (mv t f1 f2)
         (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                       formal convert-old-to-new-fn-body
                                                       iso-infos events)))
      (& (find-previous-iso-with-equivalent-definition convert-old-to-new-fn convert-new-to-old-fn
                                                       formal convert-old-to-new-fn-body
                                                       iso-infos events)))))

;;; Tries to create an isomorphism for from iso-source-pred given iso-target-pred iso-target-pred-defun.
;;; Does this by constructing the forward and backward isomorphism functions and creating a defiso event.
;;; Returns new events and the augmented iso-infos
(define make-new-iso-pred-events ((iso-source-pred symbolp)
                                  (iso-target-pred symbolp)
                                  (formals symbol-listp)
                                  old-pred-body
                                  new-pred-body
                                  (fn-infos fn-infos-list-p)
                                  (iso-infos iso-info-alist-p)
                                  (propiso-info propiso-info-p)
                                  (events true-list-listp))
  :guard-hints (("Goal" :in-theory (enable iso-info-alist-p defmapping-infop)))
  (b* (((unless (equal (length formals) 1))
        (cw "Warning: Can't handle generation of isomorphism for ~x0 (not a single formal)" iso-source-pred)
        (mv nil fn-infos iso-infos))
       (formal (first formals))
       (convert-old-to-new-fn (pack$ iso-source-pred "-->-" iso-target-pred))
       (convert-new-to-old-fn (pack$ iso-target-pred  "-->-" iso-source-pred))
       (convert-old-to-new-fn-body
        (convert-fn-for-new-iso-fn0 new-pred-body iso-target-pred formal convert-old-to-new-fn nil iso-infos))
       (convert-new-to-old-fn-body
        (convert-fn-for-new-iso-fn0 new-pred-body iso-target-pred formal convert-new-to-old-fn t iso-infos))
       ((when (or (null convert-new-to-old-fn-body) ; if 1 is null they both should be
                  (null convert-old-to-new-fn-body)))
        (cw "Warning: Can't handle generation of isomorphism for ~x0" iso-source-pred)
        (mv nil fn-infos iso-infos))
       ((mv use-old-convert-fns-p convert-old-to-new-fn convert-new-to-old-fn)
        (maybe-use-old-definitions convert-old-to-new-fn convert-new-to-old-fn
                                   formal convert-old-to-new-fn-body convert-new-to-old-fn-body
                                   iso-infos events))
       (convert-fn-defs (if use-old-convert-fns-p
                            ()
                          `((defun ,convert-new-to-old-fn ,formals ; enable ??
                              (declare (xargs :guard (,iso-target-pred ,formal)))
                              ,convert-new-to-old-fn-body)
                            (defun ,convert-old-to-new-fn ,formals ; enable ??
                              (declare (xargs :guard (,iso-source-pred ,formal)))
                              ,convert-old-to-new-fn-body))))
       (defiso-name (pack$ iso-source-pred "-ISO-" iso-target-pred))
       (defiso-form `(defiso ,defiso-name
                       ,iso-source-pred ,iso-target-pred ,convert-old-to-new-fn ,convert-new-to-old-fn
                       :hints (:beta-of-alpha
                               (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                           ,convert-old-to-new-fn ,convert-new-to-old-fn)))
                               :alpha-of-beta (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                                          ,convert-old-to-new-fn ,convert-new-to-old-fn)))
                               :alpha-image (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                                        ,convert-old-to-new-fn)))
                               :beta-image (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred
                                                                       ,convert-new-to-old-fn)))
                               ,@(and use-old-convert-fns-p
                                      `(:alpha-guard
                                        (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred)))
                                        :beta-guard
                                         (("Goal" :in-theory (enable ,iso-source-pred ,iso-target-pred))))))))
       ((unless (and (acl2::pseudo-event-formp defiso-form) ; Just so guards check!
                     (acl2::pseudo-termfnp iso-source-pred)
                     (acl2::pseudo-termfnp iso-target-pred)
                     (acl2::pseudo-termfnp convert-old-to-new-fn)
                     (acl2::pseudo-termfnp convert-new-to-old-fn)))
        (cw "Warning: Not pseudo* \n ~x0: ~x1 \n ~x2: ~x3 \n ~x4: ~x5 \n ~x6: ~x7 \n ~x8: ~x9 \n"
            (acl2::pseudo-event-formp defiso-form) defiso-form
            (acl2::pseudo-termfnp iso-source-pred) iso-source-pred
            (acl2::pseudo-termfnp iso-target-pred) iso-target-pred
            (acl2::pseudo-termfnp convert-old-to-new-fn) convert-old-to-new-fn
            (acl2::pseudo-termfnp convert-new-to-old-fn) convert-new-to-old-fn)
        (mv nil fn-infos iso-infos))
       (alpha-image (pack$ defiso-name ".ALPHA-IMAGE"))
       (beta-image (pack$ defiso-name ".BETA-IMAGE"))
       (beta-of-alpha (pack$ defiso-name ".BETA-OF-ALPHA"))
       (alpha-of-beta (pack$ defiso-name ".ALPHA-OF-BETA"))
       (alpha-injective (pack$ defiso-name ".ALPHA-INJECTIVE"))
       (beta-injective (pack$ defiso-name ".BETA-INJECTIVE"))
       (doma-guard (pack$ defiso-name ".DOMA-GUARD"))
       (domb-guard (pack$ defiso-name ".DOMB-GUARD"))
       (alpha-guard (pack$ defiso-name ".ALPHA-GUARD"))
       (beta-guard (pack$ defiso-name ".BETA-GUARD"))
       ;; Not all make-defmapping-info fields are necessary for this purpose. The defiso event will create the real one
       (new-iso-info (acl2::make-defmapping-info :call$ defiso-form
                                                 :expansion defiso-form ; place-holder to avoid guard error
                                                 :doma iso-source-pred
                                                 :domb iso-target-pred
                                                 :alpha convert-old-to-new-fn
                                                 :beta convert-new-to-old-fn
                                                 :alpha-image alpha-image
                                                 :beta-image beta-image
                                                 :beta-of-alpha beta-of-alpha
                                                 :alpha-of-beta alpha-of-beta
                                                 :alpha-injective alpha-injective
                                                 :beta-injective beta-injective
                                                 :doma-guard doma-guard
                                                 :domb-guard domb-guard
                                                 :alpha-guard alpha-guard
                                                 :beta-guard beta-guard
                                                 :unconditional nil))
       ;; Want to keep in order for new-name-maybe-using-isos
       (new-iso-infos (append iso-infos (list (cons iso-source-pred new-iso-info))))
       (convert-old-to-new-fn-type-thms (type-theorems-for-new-iso-fn new-pred-body
                                                                      formal ;; iso-source-pred
                                                                      convert-old-to-new-fn
                                                                      (and use-old-convert-fns-p iso-source-pred)
                                                                      (list `(,iso-source-pred ,formal))
                                                                      "" t new-iso-infos))
       (convert-old-to-new-fn-thm-names (theorem-names convert-old-to-new-fn-type-thms))
       (convert-new-to-old-fn-type-thms (type-theorems-for-new-iso-fn old-pred-body
                                                                      formal ;; iso-target-pred
                                                                      convert-new-to-old-fn
                                                                      (and use-old-convert-fns-p iso-target-pred)
                                                                      (list `(,iso-target-pred ,formal))
                                                                      "" nil new-iso-infos))
       (convert-new-to-old-fn-thm-names (theorem-names convert-new-to-old-fn-type-thms))
       (add-to-iso-osi-ruleset-form (add-iso-osi-theorem-event (list* alpha-image
                                                                      beta-image
                                                                      beta-of-alpha
                                                                      alpha-of-beta
                                                                      alpha-injective
                                                                      beta-injective
                                                                      ;; !! TODO: If these are trivial (normal case?) then this gives an error
                                                                      ;; doma-guard
                                                                      ;; domb-guard
                                                                      alpha-guard
                                                                      beta-guard
                                                                      (append convert-old-to-new-fn-thm-names
                                                                              convert-new-to-old-fn-thm-names))
                                                               propiso-info))
       (new-fn-infos (list* (fn-info-elt convert-old-to-new-fn nil nil nil
                                         (list iso-source-pred)
                                         (list iso-target-pred))
                            (fn-info-elt convert-new-to-old-fn nil nil nil
                                         (list iso-target-pred)
                                         (list iso-source-pred))
                            fn-infos)))
    (mv `(,add-to-iso-osi-ruleset-form ; order will be reversed
          ,@convert-new-to-old-fn-type-thms
          ,@convert-old-to-new-fn-type-thms
          ,defiso-form
          ,@convert-fn-defs)
        new-fn-infos
        new-iso-infos))
) ; make-new-iso-pred-events

; Generate events for propagating the iso refinement
; to a function introduced via DEFUN and not via DEFINE-SK.

(define propagate-iso-defun ((fun symbolp)                 ; function introduced via DEFUN and not via DEFINE-SK
                             (last-defuned-fn? symbolp)    ; If not null, then it needs to be disabled
                             (fn-renaming symbol-alistp)
                             (renaming symbol-alistp)      ; mapping of old fn and thm names to new
                             (fn-infos fn-infos-list-p)    ; mapping of old fns to new plus domain signature
                             (iso-infos iso-info-alist-p)  ; list of isomorphism 4-tuples
                             (propiso-info propiso-info-p) ; Map from theorem name to hints lists
                             (events true-list-listp)      ; events generated so far
                             (eventup acl2::pseudo-event-landmarkp)
                             state)
  ;; returns updated (mv fn-renaming renaming fn-infos iso-infos events)
  :mode :program
  (b* ((world (propiso-info->world propiso-info))
       (fun1 (new-name-maybe-using-isos fun iso-infos nil world))
       (fn-renaming1 (acons fun fun1 fn-renaming))
       (renaming (acons fun fun1 renaming))
       (events (if last-defuned-fn?  ; attempt to mimic define /// behavior
                   (cons `(in-theory (disable ,(lookup-eq last-defuned-fn? fn-renaming)))
                       events)
                 events))
       (recursivep (acl2::irecursivep+ fun world))
       (enabledp (fundef-enabledp fun state))
       ;; substitute function names in body, measure, and guard of FUN:
       (body0 (ubody fun world))
       (event-defun (cddr eventup))
       (declares (acl2::get-declares-from-defun event-defun))
       (body (fn-ubody1 fun body0 world event-defun))
       (body (clean-body body))
       (measure (and recursivep (acl2::measure+ fun world)))
       (guard-verifiedp (acl2::guards-were-verified-in-eventp event-defun))
       (old-guard (guard fun nil world))
       (old-guard (untranslate old-guard nil world))
       (old-guard-list (flatten-conj old-guard))
       (body1 (rename-fns-in-untranslated-term body fn-renaming1))
       (measure1 (rename-fns-in-untranslated-term measure fn-renaming1))
       (new-guard (rename-fns-in-untranslated-term old-guard fn-renaming1))
       ;; make body, measure, and guard of FUN' more readable: -- now just use untranslated body
       ;; (body1 (untranslate body1 nil world))
       (measure1 (untranslate measure1 nil world))
       (new-guard-list (flatten-conj new-guard))
       (user-hints (lookup-hints fun1 propiso-info))
       (skip-proofs-p (eq user-hints 'skip-proofs))
       (user-enabledp (and (consp user-hints)
                           (member (car user-hints) '(enable disable e/d))))
       (guard-hints (acl2::get-guard-hints-from-declares declares))
       (guard-hints1 (apply-renaming-to-hints guard-hints renaming))
       (guard-hints2 (if user-enabledp
                         (enable-disable-runes-in-hints guard-hints1 user-hints)
                       guard-hints1))
       (guard-hints3 (if (and user-hints (not user-enabledp))
                         user-hints
                       guard-hints2))
       (formals (formals fun world))
       ;;(old-xargs (get-xargs-from-event fun (my-get-event fun world)))
       ;;(- (cw "fn event:\n~x0\n" (my-get-event fun world)))
       ;; add DEFUN for FUN' to events:
       (xargs `(xargs ,@(if measure1 `(:measure ,measure1) ())
                      ,@(if new-guard `(:guard ,new-guard) ())
                      ,@(if guard-hints3 `(:guard-hints ,guard-hints3) ())
                      ,@(if guard-verifiedp nil `(:verify-guards nil))))
       ;;(defunp (if enabledp 'defun 'defund))  enable now but disable later see propagate-iso-defaxiom/defthm

       (event0 `(defun ,fun1 ,formals
                  (declare ,xargs)
                  ,body1))
       (event (if skip-proofs-p
                  `(skip-proofs ,event0)
                event0))
       (local-events (cons event nil))
       (install-not-normalized-event `(local (install-not-normalized ,fun1)))
       (local-events (cons install-not-normalized-event local-events))
       (fun1-not-normalized (pack$ fun1 "$NOT-NORMALIZED"))

       ;; names of the FUN = FUN' and FUN' = FUN theorems:
       (fun-is-iso-fun1 (pack$ fun '-is-iso- fun1))
       (fun1-is-iso-fun (pack$ fun1 '-is-iso- fun))
       (arg-sig (or (lookup-arg-types fun fn-infos)
                    (arg-signature formals old-guard-list iso-infos)))
       (arg-ty-alist (pairlis$ formals arg-sig))
       (ret-sig (result-signature* body fn-infos arg-ty-alist (lookup-result-types fun fn-infos)))
       ;; new-iso-pred-p means that it is a predicate that references an existing iso so we want to add it to our isos
       (new-iso-pred-p (and (equal ret-sig '(booleanp))
                            (not (dependent-on-iso-types-p arg-sig iso-infos))))
       ;; Add partial info for fun
       (fn-infos (add-fn-info-iso-fn-type fun fun1 arg-sig ret-sig fn-infos))
       ;; add correctness theorem FUN = FUN' to local-events,
       ;; proving it in the minimal theory
       ;; plus the relevant theorems above and the definition of FUN and FUN':
       (thm-formula (iso-theorem-for-fns fun fun1 formals old-guard-list arg-sig ret-sig iso-infos nil))
       ;((mv hyps &) (rule-hyps-and-conc thm-formula fun1-is-iso-fun))
       ;(bindings (find-osi-bindings hyps iso-infos))
       ;; add converse theorem fun1 iso fun, proved from the support thms and disabled:
       (conv-thm-formula (iso-theorem-for-fns fun1 fun formals new-guard-list arg-sig ret-sig iso-infos t))

       ;; get all the iso theorems for functions referenced by FUN
       ;; (these are the ones relevant to proving FUN = FUN'):
       (hyps (make-formal-conds formals arg-sig iso-infos t))
       (fun-head-tm (make-iso-osi-term fun formals arg-sig ret-sig iso-infos t))
       ((mv aux-iso-thms aux-osi-thms aux-events)
        (support-thms-for-defun body hyps fun fun1 formals ret-sig fun-head-tm
                                recursivep fn-renaming fn-infos iso-infos propiso-info))
       (local-events (if new-iso-pred-p local-events (append aux-events local-events)))
       (user-hints (lookup-hints fun1-is-iso-fun propiso-info))
       (skip-proofs-p (eq user-hints 'skip-proofs))
       (user-enabled (and (consp user-hints)
                          (member (car user-hints) '(enable disable e/d))))
       (hints (if (and user-hints (not user-enabled))
                  user-hints
                (enable-disable-runes-in-hints
                 `(("Goal" :in-theory (append ',(remove-duplicates
                                                 `(,@(if recursivep `((:induction ,fun1))
                                                       `(,fun))
                                                   ,fun1-not-normalized
                                                   (:type-prescription ,fun)))
                                              ,(osi-thm-ruleset-form propiso-info)
                                              ,(iso-osi-thm-ruleset-form propiso-info)
                                              (theory 'minimal-theory))
                    ,@(if recursivep
                          `(:induct (,fun1 ,@formals))
                        `(:use (,@aux-osi-thms ,@(if guard-verifiedp `((:guard-theorem ,fun1)) ()))))
                    :do-not-induct t)
                   ;; These get used in subgoals. Not legal in combination with :induct!
                   ,@(if recursivep
                         `('(:use (,@aux-osi-thms ,@(if guard-verifiedp
                                                        `((:guard-theorem ,fun1))
                                                      ()))))
                       nil))
                 user-hints)))
       (event (if skip-proofs-p
                  `(skip-proofs (defthmd ,fun1-is-iso-fun
                                  ,conv-thm-formula))
                (if nil  ;(implies-term? conv-thm-formula)
                    `(remove-hyps (defthmd ,fun1-is-iso-fun
                                    ,conv-thm-formula
                                    :hints ,hints)
                                  t)
                  (if (and user-hints (not user-enabled))
                      `(defthmd ,fun1-is-iso-fun
                       ,conv-thm-formula
                       :hints ,hints)
                    `(defthmd ,fun1-is-iso-fun
                       ,conv-thm-formula
                       :instructions
                       (;;(succeed (prove :hints ,hints))
                        ;; (when-not-proved (print "fn osi: prove failed!"))
                        (succeed (bash ,@hints))
                        ;; (when-not-proved (print "fn osi: bash failed!"))
                        (succeed (bash ("Goal" :in-theory
                                       (e/d* (,(propiso-info->osi-ruleset-name propiso-info))
                                             (,(propiso-info->iso-ruleset-name propiso-info))))))
                        (repeat (bash))))))))
       (local-events (if new-iso-pred-p local-events (cons event local-events)))
       ;; Add main thm fun iso fun1 proved from fun1-is-iso-fun
       (user-hints (lookup-hints fun-is-iso-fun1 propiso-info))
       (skip-proofs-p (eq user-hints 'skip-proofs))
       (user-enabled (and (consp user-hints)
                          (member (car user-hints) '(enable disable e/d))))
       (hints (if (and user-hints (not user-enabled))
                  user-hints
                (enable-disable-runes-in-hints
                 `(("Goal" :in-theory (append '(,fun1-is-iso-fun
                                                (:type-prescription ,fun)
                                                ,@aux-iso-thms)
                                              ,(iso-thm-ruleset-form propiso-info)
                                              ,(iso-osi-thm-ruleset-form propiso-info)
                                              (theory 'minimal-theory))
                    :do-not-induct t))
                 user-hints)))
       (event (if skip-proofs-p
                  `(skip-proofs (defthm ,fun-is-iso-fun1
                                  ,thm-formula))
                (if nil                 ;(implies-term? thm-formula)
                    `(remove-hyps (defthm ,fun-is-iso-fun1
                                    ,thm-formula
                                    :hints ,hints)
                                  t)
                  (if (and user-hints (not user-enabled))
                      `(defthm ,fun-is-iso-fun1
                         ,thm-formula
                         :hints ,hints)
                    `(defthm ,fun-is-iso-fun1
                       ,thm-formula
                       :instructions (;;(succeed (prove :hints ,hints))
                                      ;; (when-not-proved (print "fn iso: prove failed!"))
                                      (succeed (bash ,@hints))
                                      ;; (when-not-proved (print "fn iso: bash failed!"))
                                      (repeat (bash ("Goal" :in-theory (disable* ,(propiso-info->osi-ruleset-name propiso-info)))))))))))
       (local-events (if new-iso-pred-p local-events (cons event local-events)))
       ;; add theory invariant to prevent the two theorems
       ;; from being enabled at the same time:
       (event `(theory-invariant (incompatible (:rewrite ,fun-is-iso-fun1)
                                               (:rewrite ,fun1-is-iso-fun))))
       (local-events (if new-iso-pred-p local-events (cons event local-events)))
       (new-iso-thm-event (add-iso-theorem-event (list fun-is-iso-fun1) propiso-info))
       (new-osi-thm-event (add-osi-theorem-event (list fun1-is-iso-fun) propiso-info))
       (local-events (if new-iso-pred-p local-events (list* new-iso-thm-event new-osi-thm-event local-events)))
       ((mv new-iso-pred-events fn-infos iso-infos)
        (if new-iso-pred-p
            (make-new-iso-pred-events fun fun1 formals body body1 fn-infos iso-infos propiso-info events)
          (mv nil fn-infos iso-infos)))
       (local-events (append new-iso-pred-events local-events))
       (events (cons `(encapsulate ()
                        ,@(reverse local-events))
                     events))
       ;; Add decl info for fun
       (fn-infos (if new-iso-pred-p fn-infos
                   (add-fn-info-iso-thms fun fun-is-iso-fun1 fun1-is-iso-fun fn-infos))))
      (mv (and (not enabledp) fun)      ; returning fun here will mean that it gets disabled later
          fn-renaming1 renaming fn-infos iso-infos events))
) ; propagate-iso-defun

;; TODO: fix this for isomorphisms instead of equalities
; Generate events for propagating the iso refinement
; to a function H1 introduced via DEFINE-SK.
; Let H2 be the generated refinement of H1; H2 is also introduced via DEFINE-SK.
; To prove the iso of H1 and H2,
; we use suitable instances of the SUFF or NECC theorems of H1 and H2.
; Each instance is defined by the list of pairs
; ((BV1 (MV-NTH 0 (WITNESS FV1 ... FVn)))
;  ...
;  (BVm (MV-NTH m-1 (WITNESS FV1 ... FVn)))),
; where (BV1 ... BVm) are the m >= 2 variables bound by the quantifier
; (which are the same in H1 and H2),
; (FV1 .. FVn) are the free variables of the body
; (i.e. the parameters of H1 and H2, which are the same),
; and WITNESS is the witness of H1 or H2.
; If m = 1, there is just one pair (BV1 (WITNESS FV1 ... FVn)).

; To prove that H1 implies H2,
; we use the instance of H1-SUFF/NECC with the witness of H2.
; To prove that H2 implies H1,
; we use the instance of H2-SUFF/NECC with the witness of H1.
; This proves that H1 and H2 are IFF-equivalent.
; Since DEFINE-SK restricts H1 and H2 to return booleans,
; IFF-equivalence implies iso.

; Since DEFINE-SK does not verify guards,
; we also generate a command to verigy the guard of the new function.
; This is somewhat consistent with the fact that we generate guards
; for functions introduced via DEFUN,
; which cause guard verification,
; assuming that VERIFY-GUARD-EAGERNESS is not 0.
; We will need to extend this transformation to be more flexible
; with respect to guard verification.

(define propagate-iso-sk-pairs-aux
  ((bound-vars symbol-listp)         ; variables bound by the quantifier
   (free-vars symbol-listp)          ; formal arguments
   (witness symbolp)                 ; name of witness function
   (i natp))                         ; index of the bound variable minus 1 (= 0, ..., m-1)
  :returns (pairs true-list-listp)
  (if (endp bound-vars)
      nil
    ;; the pair is (BOUND-VAR (MV-NTH I (WITNESS FREE-VARS))):
    (let ((pair (list (car bound-vars)
                      `(mv-nth ,i (,witness ,@free-vars)))))
      (cons pair (propagate-iso-sk-pairs-aux (cdr bound-vars)
                                             free-vars
                                             witness
                                             (+ i 1))))))

(define propagate-iso-sk-pairs
  ((bound-vars symbol-listp) ; variables bound by the quantifier
   (free-vars symbol-listp) ; formal arguments
   (witness symbolp)) ; name of witness function
  :returns (pairs true-list-listp)
  (if (= (len bound-vars) 1)
      ;; just 1 pair if there is just 1 bound variable:
      (let ((bound-var (car bound-vars)))
        (list (list bound-var `(,witness ,@free-vars))))
    ;; more pairs if there are more bound variables:
    (propagate-iso-sk-pairs-aux bound-vars free-vars witness 0)))

;; TODO: This hasn't been tested or thought through
(define propagate-iso-define-sk
  ((fun symbolp) ; function introduced via DEFINE-SK
   (fn-renaming symbol-alistp)
   (renaming symbol-alistp)        ; mapping of old fn and thm names to new
   (fn-infos fn-infos-list-p)      ; mapping of old fns to new plus domain signature
   (iso-infos iso-info-alist-p)    ; list of isomorphism tuples
   (propiso-info propiso-info-p)   ; Map from theorem name to hints lists
   (events true-list-listp)        ; events generated so far
   ;; state   ; not currently needed
   )
  ;; returns updated (mv fn-renaming renaming fn-infos iso-infos events)
  :mode :program
  (b* ((world (propiso-info->world propiso-info))
       ;; use the current transformation index for FUN':
       (fun1 (new-name-maybe-using-isos fun iso-infos nil world))
       ;; add FUN and FUN' to the accumulators:
       (fn-renaming (acons fun fun1 fn-renaming))
       (renaming (acons fun fun1 renaming))
       ;; retrieve constituents of FUN:
       (guts (std::find-define-sk-guts fun world))
       (quantifier (std::define-sk-guts->quantifier guts))
       (bound-vars (std::define-sk-guts->bound-vars guts))
       (formals (formals fun world))
       (matrix (defun-sk-matrix fun world))
       ;; substitute function names in the matrix of FUN:
       (matrix1 (untranslate matrix nil world))
       (matrix1 (rename-fns-in-untranslated-term matrix1 fn-renaming))
       ;; add DEFINE-SK for FUN' to events:
       (event `(define-sk ,fun1 ,formals
                 (,quantifier ,bound-vars ,matrix1)))
       (events (cons event events))
       ;; add guard verification for FUN':
       (event `(verify-guards ,fun1))
       (events (cons event events))
       ;; get all the iso theorems for functions referenced by FUN
       ;; (these are the ones relevant to proving FUN = FUN'):
       ;; for now we assume the default names
       ;; for the witness and for the SUFF/NECC theorems
       ;; (this can be guaranteed by suitably extending DEFINE-SK):
       (witness (pack$ fun '-witness))
       (witness1 (pack$ fun1 '-witness))
       (suffix (case quantifier (forall '-necc) (exists '-suff)))
       (suff/necc (pack$ fun suffix))
       (suff/necc1 (pack$ fun1 suffix))
       (pairs (propagate-iso-sk-pairs bound-vars formals witness1))
       (pairs1 (propagate-iso-sk-pairs bound-vars formals witness))
       ;; names of the FUN = FUN' and FUN' = FUN theorems:
       (fun-is-iso-fun1 (pack$ fun '-is-iso- fun1))
       (fun1-is-iso-fun (pack$ fun1 '-is-iso- fun))
       ;; add correctness theorem FUN = FUN' to events,
       ;; proving it using the SUFF/NECC theorems
       ;; and in the minimal theory
       ;; plus the relevant theorems above and the definition of FUN and FUN':
       (hints (or (lookup-hints fun-is-iso-fun1 propiso-info)
                  `(("Goal"
                    :use ((:instance ,suff/necc ,@pairs)
                          (:instance ,suff/necc1 ,@pairs1))
                    :in-theory (append '(,fun
                                         ,fun1)
                                       (theory 'minimal-theory))))))
       (event
        `(defthm ,fun-is-iso-fun1
           (equal (,fun ,@formals) (,fun1 ,@formals))
           :hints ,hints))
       (events (cons event events))
       ;; add converse theorem FUN' = FUN,
       ;; proved from the previous one
       ;; and disabled:
       (hints (or (lookup-hints fun1-is-iso-fun propiso-info)
                  `(("Goal" :in-theory (cons ',fun-is-iso-fun1
                                                  (theory 'minimal-theory))))))
       (event `(defthmd ,fun1-is-iso-fun
                 (equal (,fun1 ,@formals) (,fun ,@formals))
                 :hints ,hints))
       (events (cons event events))
       ;; add theory invariant to prevent the two theorems
       ;; from being enabled at the same time:
       (event `(theory-invariant (incompatible (:rewrite ,fun-is-iso-fun1)
                                               (:rewrite ,fun1-is-iso-fun))))
       (events (cons event events))
       ;; add FUN = FUN' to accumulator:
       (fn-infos (acons fun fun-is-iso-fun1 fn-infos)))
      (mv fun fn-renaming renaming fn-infos iso-infos events)))

(defun references-in-tree-p (items tree)
  (or (member-equal tree items)
      (and (consp tree)
           (or (references-in-tree-p items (car tree))
               (references-in-tree-p items (cdr tree))))))

(defun usable-hints-p (hints)
  (references-in-tree-p '(:functional-instance :by) hints))

; Generate events for propagating the iso refinement
; to an axiom or theorem (which are treated in the same way).

(define propagate-iso-defaxiom/defthm
  ((thm symbolp)                        ; name of axiom or theorem
   (last-defuned-fn? symbolp)           ; if non-null maybe defined using define, so may need disabling
   (fn-renaming symbol-alistp)
   (renaming symbol-alistp)             ; mapping of old fn and thm names to new
   (fn-infos fn-infos-list-p)           ; mapping of old fns to new plus domain signature
   (iso-infos iso-info-alist-p)         ; list of isomorphism 4-tuples
   (propiso-info propiso-info-p)            ; Map from theorem name to hints lists
   (eventup acl2::pseudo-event-landmarkp)
   (events true-list-listp)            ; events generated so far
   state)
  ;; returns updated (mv last-defuned-fn? fn-renaming renaming fn-infos iso-infos events)
  ;; todo: also return old name to new name mapping
  :mode :program
  (b* ((world (propiso-info->world propiso-info))
       (formula0 (formula thm nil world))
       (formula (untranslate formula0 nil world))
       (used-old-fns (filter-assoc (get-called-fns-in-untranslated-term formula)
                                   fn-renaming))
       ((when (null used-old-fns))
        ;; ?? Ignore theorems just on domain predicates; alt prove with translated hints
        (mv last-defuned-fn? fn-renaming renaming fn-infos iso-infos events))

       (old-hints (second (member-eq ':hints eventup)))
       (thm-enabledp (acl2::rune-enabledp `(:rewrite ,thm) state))
       (thm1 (new-name-maybe-using-isos thm iso-infos t world))
       (renaming (acons thm thm1 renaming))
       ;; retrieve formula and rule classes of THM:
       (classes (acl2::classes thm world))
       (classes (classes-subst classes fn-renaming))
       ;; (- (if (eq thm 'list::memberp-but-not-cdr-drone-ids)
       ;;        (cw "thm event:~%~x0~%" (my-get-event thm world))
       ;;      ()))
       ;; substitute function names in the formula of THM:
       (formula1 (rename-fns-in-untranslated-term formula fn-renaming))
       ;; get all the iso theorems for functions referenced by THM
       ;; (these are the ones relevant to proving THM'):
       ((mv & head) (rule-hyps-and-conc formula thm))                       ; hyps
       (disable-last-defuned-fn (and last-defuned-fn? (not (member-equal last-defuned-fn? used-old-fns))))
       (events (if disable-last-defuned-fn
                   (cons `(in-theory (disable ,(lookup-eq last-defuned-fn? fn-renaming))) ; attempt to recapitulate define behavior
                       events)
                 events))
       (bindings (variable-osi-subst (variable-types formula fn-infos iso-infos ())
                                     iso-infos))
       ;; (checked-bindings (find-iso-bindings hyps iso-infos))
       (user-hints (lookup-hints thm1 propiso-info))
       (skip-proofs-p (eq user-hints 'skip-proofs))
       (user-enabledp (and (consp user-hints)
                           (equal (car user-hints) 'enable)))
       (user-enabled (and user-enabledp (cdr user-hints)))
       (new-hints (if (and user-hints (not user-enabledp))
                      user-hints
                    `(("Goal"
                         :use (:instance ,thm ,@bindings)
                         :in-theory (append ',user-enabled
                                            ,(osi-thm-ruleset-form propiso-info)
                                            ,(iso-osi-thm-ruleset-form propiso-info)
                                            (theory 'minimal-theory))))))
       ;; add DEFTHM for THM' to events,
       ;; proving it using THM with argument reverse iso translation
       ;; and in the minimal theory plus the relevant theorems above:
       (defthm-d? (if thm-enabledp 'defthm 'defthmd))
       (event (if skip-proofs-p
                  `(skip-proofs (,defthm-d? ,thm1
                                  ,formula1
                                  :rule-classes ,classes))
               (if (and user-hints (not user-enabledp))
                   `(,defthm-d? ,thm1
                      ,formula1
                      :rule-classes ,classes
                      :hints ,new-hints)
                 `(,defthm-d? ,thm1
                    ,formula1
                    :rule-classes ,classes
                    :instructions ((succeed (prove :hints ,(apply-renaming-to-hints old-hints renaming)))
                                   ;; (when-not-proved (print "thm: reprove failed!"))
                                   ;(succeed (prove :hints ,new-hints))
                                   ;; (when-not-proved (print "thm: prove failed!"))
                                   (succeed (bash ,@new-hints))
                                   ;; (when-not-proved (print "thm: bash failed!"))
                                   (repeat (bash ("Goal" :in-theory (disable* ,(propiso-info->iso-ruleset-name propiso-info)))))
                                   )))))
       (events (cons event events))
       (typed-fn (type-theorem-p head))
       (add-to-rule-set-form (if typed-fn
                                 (add-iso-osi-theorem-event (list thm1) propiso-info)
                               nil))
       (events (if add-to-rule-set-form
                   (cons add-to-rule-set-form events)
                 events)))
    (mv (and (not disable-last-defuned-fn)
             last-defuned-fn?)
        fn-renaming renaming fn-infos iso-infos events))
) ; propagate-iso-defaxiom/defthm

;; Generate events for propagating the iso refinement to a VERIFY-GUARDS.
;; TODO: needs testing
(define propagate-iso-verify-guards
  ((old-fun symbolp)
   (fn-renaming symbol-alistp)
   (renaming symbol-alistp)      ; mapping of old fn and thm names to new
   (fn-infos fn-infos-list-p)    ; mapping of old fns to new plus rewrite thm and domain signature
   (iso-infos iso-info-alist-p)  ; map of domain to isomorphism info
   (events true-list-listp)) ; events generated so far
  ;; returns updated (mv nil fn-renaming renaming fn-infos iso-infos events)
  :mode :program
  (b* (;; replace H with its refinement H', if there is one:
       (new-fun (rename-fns-in-untranslated-term old-fun fn-renaming))
       ;; if H' is the same as H, then H does not depend on F1
       ;; and thus no VERIFY-GUARDS event needs to be generated;
       ;; otherwise we generate a VERIFY-GUARDS event for H':
       ;; todo: translate hints
       (events (if (eq old-fun new-fun)
                   events
                 (cons `(verify-guards ,new-fun) events))))
      (mv nil fn-renaming renaming fn-infos iso-infos events)))


;; Scan events and generate refinement events.

(define propagate-iso-loop
  ((eventups acl2::pseudo-event-landmark-listp)  ; event tuples to process, chronological order
   (last-defuned-fn symbolp)
   (fn-renaming symbol-alistp)          ; mapping of old fn names to new
   (renaming symbol-alistp)             ; mapping of old fn and thm names to new
   (fn-infos fn-infos-list-p)           ; mapping of old fns to new plus rewrite thm and domain signature
   (iso-infos iso-info-alist-p)         ; mapping from isomorphism names to isomorphism records
   (propiso-info propiso-info-p) ; Map from theorem name to hints lists
   (events true-listp)                  ; generated events, reverse chronological order
   state)
  ;; returns list of events and final iso-infos and fn-infos
  :mode :program
  (if (endp eventups)
      (mv events iso-infos fn-infos)
    ;; process event tuple according to type:
    (let ((eventup (car eventups))
          (world (propiso-info->world propiso-info)))
      (mv-let (last-defuned-fn fn-renaming+ renaming+ fn-infos+ iso-infos+ events+)
          (case (acl2::access-event-tuple-type eventup)
            (defun
                (let ((fun (acl2::access-event-tuple-namex eventup)))
                  (if (assoc fun fn-renaming)
                      (mv last-defuned-fn fn-renaming renaming fn-infos iso-infos events) ; ignore functions that are part of propagate-iso form
                    (if (std::find-define-sk-guts fun world)
                        (propagate-iso-define-sk fun fn-renaming renaming fn-infos iso-infos propiso-info events ;; state
                                                 )
                      (propagate-iso-defun fun last-defuned-fn fn-renaming renaming fn-infos iso-infos propiso-info events eventup state)))))
            (defuns
              (prog2$ (raise "Event tuple ~x0 not supported." eventup)
                      (mv nil nil nil nil nil nil)))
            ((defaxiom defthm)
             (let ((thm (acl2::access-event-tuple-namex eventup)))
               (propagate-iso-defaxiom/defthm thm last-defuned-fn fn-renaming renaming fn-infos iso-infos propiso-info eventup events state)))
            (verify-guards
              (let* ((form (acl2::access-event-tuple-form eventup))
                     (fun (cadr form)))
                (propagate-iso-verify-guards fun fn-renaming renaming fn-infos iso-infos events)))
            (otherwise
             (prog2$ (raise "Unexpected event tuple ~x0." eventup)
                     (mv nil nil nil nil nil nil))))
        ;; process remaining event tuples, with updated accumulators:
        (propagate-iso-loop
         (cdr eventups) last-defuned-fn fn-renaming+ renaming+ fn-infos+ iso-infos+ propiso-info events+ state)))))


;; Propagate isomorphisms

(define propagate-iso-events
  ((iso-infos iso-info-alist-p) ; isomorphism info
   (fn-infos fn-infos-list-p)  ; function translation and domain info
   (event-regions symbol-alistp)
   (dont-verify-guards booleanp)
   (result-type-map symbol-alistp)
   (propiso-info propiso-info-p)            ; Map from theorem name to hints lists
   (extra-seed-fns symbol-listp)
   state)
  ;; returns list of events
  :mode :program
  :ignore-ok t ; TODO: delete
  (b* ((world (propiso-info->world propiso-info))
       ;; take event tuples from iso sources to last-event:
       (eventups (acl2::event-tuples-between (append extra-seed-fns (source-fns fn-infos) (strip-cars iso-infos))
                                       (list (cdar (last event-regions))) world))
       ;; if there are no event tuples, G1 does not depend on F1:
       ((if (eq eventups nil))
        (raise "~x0 does not depend on isomorphisms." (cdar (last event-regions)))
        (mv nil nil nil))
       ;; since the first event tuple introduces F1,
       ;; for which we already have the refinement F2,
       ;; we skip the first event tuple and start with the next one:
       (eventups (event-tuples-between-pairs event-regions eventups))
       (fn-renaming (append (pairlis$ (strip-cars iso-infos) (map-iso-domb iso-infos))
                            (pairlis$ (source-fns fn-infos) (target-fns fn-infos))))
       (renaming (append (renaming-from-fn-infos fn-infos)
                         (renaming-from-iso-infos iso-infos)))
       (fn-infos (incorporate-iso-infos iso-infos fn-infos))
       (fn-infos (incorporate-result-type-map result-type-map fn-infos))
       ((mv fn-infos typing-thms) (result-types-from-theorems eventups fn-infos iso-infos () world))
       (typing-thm-event (add-iso-osi-theorem-event typing-thms propiso-info))
       ;; propagate the refinement to all event tuples:
       ((mv events iso-infos fn-infos)
        (propagate-iso-loop eventups nil fn-renaming renaming fn-infos iso-infos propiso-info (list typing-thm-event) state)))
      ;; arrange in chronological order:
      (mv (reverse events) iso-infos fn-infos)))


;; Input-checking/processing functions

(define check-isos ((isos symbol-listp) (world plist-worldp))
  :mode :program
  (if (endp isos)
      ()
    (let* ((iso-name (first isos))
           (iso-info (defiso-lookup iso-name world)))
      (if (null iso-info)
          (raise "~x0 must be an isomorphism name." (first isos))
        (acons (acl2::defmapping-info->doma iso-info)
               iso-info
               (check-isos (rest isos) world))))))

(defmap iso-names-from-iso-info-alist-p (info-elts)
  (and (iso-info-iso-name (cdr info-elts)))
  :declares ((xargs :guard (iso-info-alist-p info-elts))))

(define print-iso-infos ((iso-infos iso-info-alist-p))
  (cw "Final isos: ~x0~%" (iso-names-from-iso-info-alist-p iso-infos)))

(defmacro raise-mv-t (&rest args)
  `(prog2$ (raise ,@args)
           (mv t nil)))

(define check-fn-infos1 (fn-info (iso-infos iso-info-alist-p) (world plist-worldp))
  (case-match fn-info
    ((fn-i t-fn-i iso-thm osi-thm arg-types (quote~ =>) result-ty)
     (cond ((not (and (symbolp fn-i)
                      (or (function-symbolp fn-i world)
                          (acl2::macro-symbolp fn-i world))))
            (raise-mv-t "~x0 must be a function." fn-i))
           ((not (and (symbolp t-fn-i)  ; Todo: Check arities are the same!
                      (or (function-symbolp t-fn-i world)
                          (acl2::macro-symbolp t-fn-i world))))
            (raise-mv-t "~x0 must be a function." t-fn-i))
           ((not (and (symbolp iso-thm)
                      (acl2::theorem-symbolp iso-thm world)))
            (raise-mv-t "~x0 must be a theorem." iso-thm))
           ((not (and (symbolp osi-thm)
                      (acl2::theorem-symbolp osi-thm world)))
            (raise-mv-t "~x0 must be a theorem." osi-thm))
           ((not (and (symbol-listp arg-types)
                      (valid-iso-domain-list-p arg-types iso-infos)))
            (raise-mv-t "~x0 must be a list of isomorphism predicates or *." arg-types))
           ((not (if (symbolp result-ty)
                     (or (valid-iso-domain-p result-ty iso-infos)
                         (equal result-ty 'booleanp))
                   (and (symbol-listp result-ty)
                        (valid-iso-domain-list-p result-ty iso-infos))))
            (raise-mv-t "~x0 must be a predicates or * a list of such." result-ty))
           (t (mv nil (fn-info-elt fn-i t-fn-i iso-thm osi-thm arg-types (if (symbolp result-ty)
                                                                             (list result-ty)
                                                                           result-ty))))))
    (& (raise-mv-t "~x0 must be of the form (fn-i fn-i' iso-thm osi-thm (.. arg-type-i ..) => result-ty)." fn-info))))

(define check-fn-infos (fn-infos (iso-infos iso-info-alist-p) (world plist-worldp))
  (if (atom fn-infos)
      (mv nil ())
    (b* (((mv erp v1) (check-fn-infos1 (first fn-infos) iso-infos world))
         ((when erp) (mv t nil))
         ((mv erp rv) (check-fn-infos  (rest fn-infos) iso-infos world))
         ((when erp) (mv t nil)))
      (mv nil (cons v1 rv)))))

(define print-fn-infos-aux ((fn-infos fn-infos-list-p))
  (if (endp fn-infos)
      nil
    (let ((fn-info-elt (car fn-infos)))
      (progn$ (cw "(~x0 ~x1~%   ~x2 ~x3~%   ~x4 => ~x5)~%  "
                  (fn-info-elt->source-fn fn-info-elt)
                  (fn-info-elt->target-fn fn-info-elt)
                  (fn-info-elt->iso-thm fn-info-elt)
                  (fn-info-elt->osi-thm fn-info-elt)
                  (fn-info-elt->arg-types fn-info-elt)
                  (fn-info-elt->result-types fn-info-elt))
              (print-fn-infos-aux (cdr fn-infos))))))

(defthm reverse-fn-infos-list-p
  (implies (fn-infos-list-p l)
           (fn-infos-list-p (reverse l)))
  :hints (("Goal" :in-theory (enable fn-infos-list-p reverse))))

(define print-fn-infos ((fn-infos fn-infos-list-p))
  (progn$ (cw "fn-info:~%(")
          (print-fn-infos-aux (reverse fn-infos))
          (cw ")")))

;; May need extending
(defconst *general-rules*
  '(acl2::car-cons acl2::cdr-cons not atom))

;; Core of the transformation.
;; The user supplies the name of the isos and optionally the name of a top-level function last-event.
;; The isomorphisms are propagated to last-event or all dependent functions if last-event is omitted..

(define propagate-iso-event (isos fn-infos
                                  (first-event symbolp)
                                  (last-event symbolp)
                                  (event-regions symbol-alistp)
                                  (dont-verify-guards booleanp)
                                  result-type-map
                                  extra-seed-fns ; TODO check symbol-listp of fns
                                  enabled
                                  iso-rules
                                  osi-rules
                                  hints-map
                                  print-tables
                                  print
                                  ctx
                                  state)
  ;; returns list of events
  :mode :program
  (declare (ignorable print ctx))
  (b* ((world (w state))
       ;; ensure that isos is an isomorphism name or list of isomorphism names:
       ((unless (or (symbolp isos)
                    (and (symbol-listp isos)
                         isos)))
        (raise "~x0 must be an isomorphism name or list of isomorphism names." isos)
        (mv t nil state))
       (iso-infos (check-isos (if (symbolp isos)
                                  (list isos)
                                isos)
                              world))
       (main-iso-name (if (consp isos)
                          (car isos)
                        isos))
       ((unless iso-infos)
        (raise "No isomorphisms to apply!")
        (mv t nil state))
       ((mv erp fn-infos) (check-fn-infos fn-infos iso-infos world))
       ((when erp)
        (mv t nil state))
       ((unless (symbolp first-event))
        (raise "~x0 must be a symbol." first-event)
        (mv t nil state))
       (iso-osi-ruleset-name (pack$ main-iso-name "-ISO-OSI-THMS"))
       (initial-iso-osi-rules (append (iso-convert-theorems iso-infos) enabled *general-rules*))
       (iso-ruleset-name (pack$ main-iso-name "-ISO-THMS"))
       (initial-iso-rules (append (iso-thms fn-infos) iso-rules))
       (osi-ruleset-name (pack$ main-iso-name "-OSI-THMS"))
       (initial-osi-rules (append (osi-thms fn-infos) osi-rules))
       (propiso-info (propiso-info iso-osi-ruleset-name iso-ruleset-name osi-ruleset-name (doublets-to-alist hints-map)
                                   world))
       (event-regions (doublets-to-alist event-regions))
       (event-regions (if first-event
                          (acons first-event last-event event-regions)
                        event-regions))
       ;; generate events to propagate F1 = F2 to G1:
       ((mv events iso-infos fn-infos)
        (propagate-iso-events iso-infos fn-infos event-regions dont-verify-guards result-type-map
                              propiso-info extra-seed-fns state))
       ((when print-tables)
        (print-iso-infos iso-infos)
        (print-fn-infos fn-infos)
        (mv t nil state)))
    (value `(encapsulate ()
              (logic)
              (set-ignore-ok t)
              (set-irrelevant-formals-ok t)
              (set-default-hints nil)
              (set-override-hints nil)
              (def-ruleset! ,iso-osi-ruleset-name ',initial-iso-osi-rules)
              (def-ruleset! ,iso-ruleset-name ',initial-iso-rules)
              (def-ruleset! ,osi-ruleset-name ',initial-osi-rules)
              ,@events))))


(deftransformation propagate-iso
  (isos fn-infos)
  ((first-event 'nil)
   (last-event 'nil)
   (event-regions 'nil)
   (dont-verify-guards 'nil) ; nil means do the default, t means add :verify-guards nil
   (result-type-map 'nil)
   (extra-seed-functions 'nil)
   (enabled 'nil)
   (iso-rules 'nil)
   (osi-rules 'nil)
   (hints-map 'nil)
   (print-tables 'nil))
  :pass-print t
  :pass-context t)


;; See tests in propagate-iso-tests-i.lisp for i=1,2,3

#| Notes
remove-hyps: Conditions on isomorphism theorems for new functions. All guards of guards involving isomorphism preds?
  Should behave the same on arguments that aren't involved in the isomorphism?
|#
