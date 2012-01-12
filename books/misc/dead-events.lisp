; Dead events (dead code and theorems) analysis tool
; Initial author:
;   Matt Kaufmann
;   January, 2012

; For some relevant background, see :DOC dead-events in the ACL2
; documentation.

; Example use:
; cd ../workshops/1999/compiler/
; [Start ACL2]
; (ld "proof.lisp")
; (include-book "misc/dead-events" :dir :system)
; (dead-events '(compiler-correctness-for-programs) :start 'function-callp)
; After commenting out all events in proof.lisp with names in the list returned
; by the above call of dead-events, the resulting book was still certifiable.

; Example invocations:

; (dead-events '(foo bar))
; - Find the names of all function symbols and theorems that do not participate
;   in the proofs of admission of foo and bar.  Even "syntactic supporters" are
;   considered to "participate": function symbols f that occur in the formulas
;   of foo or bar, function symbols that occur in the formulas of all such f,
;   and so on.

; (dead-events '(foo bar) :syntaxp nil)
; - Find all supporters of the proofs of admission of foo and bar, but without
;   adding "syntactic supporters" as defined above.

; (dead-events '(foo bar) :start 'start-of-events-label)
; - With the above :start argument, the events returned are restricted to those
;   that are as recent as the event named start-of-events-label.

; General specification:

; The macro (dead-events lst) is defined at the end of this book, where lst
; should evaluate to a list of event names, and the result is a list of event
; names for dead code and dead theorems: names of function and theorems that do
; not support the proof of any event in lst.

; By default, or if keyword :syntaxp t is provided, "support the proof of event
; E" is interpreted broadly: it includes not only the names of rules and hinted
; events (from :use, :by, or :clause-processor hints) that are used by the
; prover when admitting E, but also function symbols ancestral in the formula
; of event E.  However, if keyword argument :syntax nil is provided, then only
; the former are included, not the ancestral function symbols.

; It may be useful to provide a keyword argument, :start.  When that argument
; is evaluated, its value should be the name E of an event, and only events at
; least as recent as E will be returned.

; NOTES:

; - Please feel free to extend or otherwise improve this book!

; - This tool is to be run in a world that was created without skipping proofs.
;   More complete documentation will likely come later.

; - This code may not work as expected if there has been redefinition.

; - If you want to read the code below, it may be helpful to go top-down.  Some
;   key data structures passed around are as follows.

;   supp-ar: an array whose keys are absolute-event-numbers.  Each key is
;   mapped to the absolute-event-numbers of supporting events.

;   live-names-ar: an array whose keys are absolute-event-numbers.  All keys
;   are initially mapped to nil, but as we see that a key k is the
;   absolute-event-number of a non-dead event, we map k to t.

; TO DO:

; - Generalize notion of "syntactic supporter"; see the WARNING in
;   immediate-syntactic-supporters-lst.

; - Improve efficiency by using "start" argument of dead-events-fn to limit
;   building of the transitive closure.

(in-package "ACL2")

(program)

(defun absolute-event-number (namex wrld quietp)

; If quietp is nil then we insist on an absolute event number; otherwise we are
; allowed to return nil.

  (let ((name (if (consp namex) (car namex) namex)))
    (cond ((getprop name
                    'absolute-event-number
                    nil
                    'current-acl2-world
                    wrld))
          (quietp nil)
          (t (er hard 'absolute-event-number
                 "There is no event in the current ACL2 world that ~
                  corresponds to the name ~x0."
                 name)))))

(defconst *supp-ar-name* 'supp-ar)

(defun strict-merge-> (l1 l2)

; Given l1 and l2, strictly decreasing lists of rationals, the result is their
; merge into a strictly decreasing list without duplicates.

  (cond ((null l1) l2)
        ((null l2) l1)
        ((eql (car l1) (car l2))
         (cons (car l1)
               (strict-merge-> (cdr l1) (cdr l2))))
        ((> (car l1) (car l2))
         (cons (car l1) (strict-merge-> (cdr l1) l2)))
        (t (cons (car l2) (strict-merge-> l1 (cdr l2))))))

(defun strict-merge-sort-> (l)

; For a list l of rational numbers, this function returns a list in strictly
; decreasing order that has the same members as l.

  (cond ((null (cdr l)) l)
        (t (let ((n (floor (len l) 2)))
             (strict-merge-> (strict-merge-sort-> (take n l))
                             (strict-merge-sort-> (nthcdr n l)))))))

(defun make-supp-ar-2 (nums new-nums supp-ar)
  (cond ((endp nums) new-nums)
        (t (let* ((k (car nums))
                  (new-nums (strict-merge-> (aref1 *supp-ar-name* supp-ar k)
                                            new-nums)))
             (make-supp-ar-2 (cdr nums) new-nums supp-ar)))))

(defun absolute-event-number-lst (lst wrld)
  (cond ((endp lst) nil)
        (t (cons (absolute-event-number (car lst) wrld nil)
                 (absolute-event-number-lst (cdr lst) wrld)))))

(defun immediate-syntactic-supporters-lst (fns wrld acc)

; WARNING: This function is incomplete.  To be complete we should really
; account for guards, siblings (i.e. other functions in the same
; mutual-recursion nest), and the 'classes property for theorems.

  (cond
   ((endp fns) acc)
   ((function-symbolp (car fns) wrld)
    (immediate-syntactic-supporters-lst
     (cdr fns)
     wrld
     (append (remove1 (car fns)
                      (immediate-instantiable-ancestors (car fns) wrld nil))
             acc)))
   (t (let ((thm (getprop (car fns) 'theorem nil 'current-acl2-world wrld)))
        (immediate-syntactic-supporters-lst
         (cdr fns)
         wrld
         (if thm (all-ffn-symbs thm acc) acc))))))

(defun make-supp-ar-1 (flg supp-alist supp-ar wrld)
  (cond ((endp supp-alist) supp-ar)
        (t
         (let* ((n (absolute-event-number (caar supp-alist) wrld nil))
                (supp-ar (make-supp-ar-1 flg (cdr supp-alist) supp-ar wrld))
                (supps (cdar supp-alist))
                (actual-supps (if flg
                                  (immediate-syntactic-supporters-lst
                                   supps wrld supps)
                                supps))
                (nums (strict-merge-sort->
                       (absolute-event-number-lst actual-supps wrld)))
                (nums (if (eql (car nums) n) (cdr nums) nums))
                (new-nums (make-supp-ar-2 nums nums supp-ar)))
           (aset1 *supp-ar-name* supp-ar n new-nums)))))

(defun max-supp-alist-event-number (supp-alist wrld acc)

; Supp-alist is a proof-supporters-alist (see :DOC dead-events in the ACL2
; documentation).

  (cond ((endp supp-alist) acc)
        (t (max-supp-alist-event-number
            (cdr supp-alist)
            wrld
            (max acc

; We needn't worry about (cdar supp-alist), since presumably all
; absolute-event-numbers for its members are no greater than that of (caar
; supp-alist).

                 (absolute-event-number (caar supp-alist) wrld nil))))))

(defun make-supp-ar (flg wrld)

; The proof-supporters-alist of wrld, supp-alist, is an alist with entries of
; the form (namex . names), where namex is a symbol or list of symbols and
; names is a list of symbols.  We return an array supp-ar, with the following
; properties.  First, note that supp-alist defines a relation, R, where R(x,y)
; is true when for some (namex . names) in supp-alist, x is namex or (if namex
; is a list) x is a member of namex, and y is a member of names.  For such x
; and y, let nx and ny be their (respective) absolute-event-numbers.  Then the
; domain of supp-ar is the set of all nx for x in the domain of R, and supp-ar
; maps each such nx to a list of all ny such that R(x,y).

; If flg is t then the relation R(x,y) is considered to hold when y
; syntactically supports x (ancestrally).  For example, if a theorem x uses a
; rule based on event x1, which mentions function symbol x2, which is supported
; in proof by x3, which names an event that mentions function symbol y, then
; R(x,y).

  (let* ((supp-alist (global-val 'proof-supporters-alist wrld))
         (size (1+ (max-supp-alist-event-number supp-alist wrld 0))))
    (make-supp-ar-1 flg
                    supp-alist
                    (compress1 *supp-ar-name*
                               (list (list :HEADER
                                           :DIMENSIONS (list size)
                                           :MAXIMUM-LENGTH (1+ size)
                                           :DEFAULT nil
                                           :NAME *supp-ar-name*)))
                    wrld)))

(defconst *live-names-ar-name* 'live-names-ar)

(defun aset1-t (name ar n)
  (cond ((aref1 name ar n) ar)
        (t (aset1 name ar n t))))

(defun aset1-t-lst (name ar lst)
  (cond ((endp lst) ar)
        (t (aset1-t-lst name
                        (aset1-t name ar (car lst))
                        (cdr lst)))))

(defun make-live-names-ar-1 (names supp-ar live-names-ar wrld)
  (cond ((endp names) live-names-ar)
        (t (let* ((n (absolute-event-number (car names) wrld nil))
                  (live-names-ar
                   (aset1-t *live-names-ar-name* live-names-ar n))
                  (supps (aref1 *supp-ar-name* supp-ar n))
                  (live-names-ar
                   (aset1-t-lst *live-names-ar-name* live-names-ar supps)))
             (make-live-names-ar-1 (cdr names) supp-ar live-names-ar wrld)))))

(defun make-live-names-ar (names supp-ar wrld)
  (let* ((dimensions (dimensions *supp-ar-name* supp-ar))
         (maximum-length (maximum-length *supp-ar-name* supp-ar))
         (live-names-ar (compress1 *live-names-ar-name*
                                   (list (list :HEADER
                                               :DIMENSIONS dimensions
                                               :MAXIMUM-LENGTH maximum-length
                                               :DEFAULT nil
                                               :NAME *live-names-ar-name*)))))
    (make-live-names-ar-1 names supp-ar live-names-ar wrld)))

(defun dead-events-1 (start live-names-ar trips wrld acc)

; Trips is a tail of the current logical world, wrld.  We walk through trips,
; collecting dead event names into acc.  Live-names-ar is an array that maps
; live event names (only) to t.

  (cond ((null trips)
         (er hard 'dead-events-1
             "Implementation error!  Somehow missed event landmark for ~x0."
             start))
        (t (let ((trip (car trips)))
             (case-match trip
               (('event-landmark 'global-value . rest)
                (cond
                 ((eql (access-event-tuple-number rest) start)
                  acc)
                 (t (dead-events-1 start live-names-ar (cdr trips) wrld acc))))
               ((name prop . &)
                (dead-events-1
                 start live-names-ar (cdr trips) wrld
                 (if (and (member-eq prop '(formals theorem))
                          (let ((n (absolute-event-number name wrld t)))
                            (and n
                                 (not (aref1 *live-names-ar-name* live-names-ar
                                             n)))))
                     (cons name acc)
                   acc)))
               (& (er hard 'dead-events-1
                      "Implementation error: Found non-triple in world!")))))))

(defun dead-events-fn (names syntaxp start wrld)
  (let* ((ctx 'dead-events)
         (supp-ar (make-supp-ar syntaxp wrld))
         (start (cond ((symbolp start)
                       (if start

; We subtract 1 here because we need to continue past the event-landmark for
; start (which is laid down last, towards the top of the world) up to the
; preceding event-landmark.

                           (1- (absolute-event-number start wrld nil))
                         (absolute-event-number 'end-of-pass-2 wrld nil)))
                      ((posp start) (1- start))
                      (t (er hard ctx
                             "The first argument of dead-events must evaluate ~
                              to a positive integer or a symbol, but ~x0 is ~
                              neither."
                             start))))
         (live-names-ar (make-live-names-ar names supp-ar wrld)))
    (dead-events-1 start live-names-ar wrld wrld nil)))

(defmacro dead-events (names &key (syntaxp 't) start)
  `(dead-events-fn ,names ,syntaxp ,start (w state)))

(logic)
