; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is a patch to load into raw Lisp before saving an executable to use with
; acl2data.lisp.  It was developed with respect to the following version of
; ACL2; also see original.lsp for the unmodified ACL2 source function (for that
; version of ACL2) corresponding to each modified ACL2 source function below.

#|
~/acl2/acl2-git-scratch$ git rev-parse HEAD
8378f7a9f694340fd73aa37c210761c237c42420
~/acl2/acl2-git-scratch$
|#

; See file README in this directory.

; 6/2022: For run7 there are the following changes from run6.
#|
(1) Include the original theorem with keyword :EVENT.

(2) Add a :RULE-CLASSES field for the original theorem, default
    (:REWRITE).

(3) Indicate the "broken theorem" for hint or hypothesis removal, but
    not book-runes or one-rune-at-a-time removal (where "broken
    theorem" doesn't really make sense).  WARNING: the broken theorem is
    obtained only by changing the body of the original theorem, not other
    fields (in particular, not corollaries).

(4) Show each list of checkpoints both as clauses (implicit
    disjunctions) in translated (internal) form -- as has been done so
    far -- and also as corresponding terms in untranslated form, as
    are displayed to users during a proof attempt.

(5) For hypothesis removal, don't remove syntaxp or bind-free
    hypotheses, since these are there for a reason even though
    logically they are irrelevant.

(6) Previously, the keys for hypothesis removal didn't account for superior
    LET-bindings; that has been fixed.  This has been fixed in a brute-force
    way: we no longer remove hypotheses that are under let-bindings.  (The idea
    is that these are likely to be too complicated to be helpful in suggesting
    repairs.)  With this change, we also add, after the broken theorem, the
    untranslated hypothesis that was removed.  Before removing hypotheses we
    apply trivial transformations: (implies h1 (implies h2 c)) becomes
    (implies (and h1 h2) c), and hypotheses are flattened, e.g., (implies (and
    h1 (and h2 h3) h4) c) becomes (implies (and h1 h2 h3 h4) c).  This of
    course introduces a bit of discrepancy between the shape of the new
    theorems and the shape of the original theorem, but that difference seems
    trivial and if someone asks I could do the work to restore the original
    structure.

Also, a technical change that for a theorem (implies H C), when we remove H
then the broken theorem submitted is C, where formerly it was (implies t C).
For an example see textbook/chap11/finite-sets.lisp, cons-preserves-subset.
Formerly we had this entry:

   (CONS-PRESERVES-SUBSET
        (:GOAL (IMPLIES (=< X Y) (=< X (CONS A Y))))
        (:USED-INDUCTION T)
        (:HYP-ALIST (((=< X Y)
                      (((IMPLIES 'T (=< X (CONS A Y)))))
      ....

Now (IMPLIES 'T (=< X (CONS A Y))) is replaced by (=< X (CONS A Y)).

|#

; 6/2022: For run6, retry with removal of everything I've considered so far:
; hyp, hint, book-runes, single-runes.

; 5/2022: Only remove book-runes.  Code that formerly was conditioned on
; #+acl2-runes is now restored, but is for remove-book-runes-checkpoints rather
; than remove-rune-checkpoints.  Many uses of rune-alist below now reference an
; alist mapping book names (generally relativized to "[books]/") to rune lists,
; rather than whatever rune-alist was for the obsolete remove-rune-checkpoints
; code, which is somewhat out of date.

; 4/2022: Restricted to removing hypotheses and hints, not runes.  In case we
; want to remove runes again, we are using feature :acl2-runes to mark code
; that should be included if we want to include rune removal.

; Warning: Keep this in sync with the include-book forms in patch-book.lisp.
(include-book "remove-hyp-checkpoints")
(include-book "remove-hint-setting-checkpoints")
(include-book "remove-rune-checkpoints")
(include-book "remove-book-runes-checkpoints")
(include-book "count-acl2data")
(include-book "event-symbol-table")
(reset-prehistory) ; avoid losing these with certify-book!.

(defun acl2data-time-limit (time)

; This is adapted from remove-hyps-formula-steps in tools/remove-hyps.  We
; might want to use a bigger limit here, since if we run out of time too soon
; then we won't see any (or enough) interesting checkpoints.  But then the runs
; might take a long time.

; The minimum of 1/20 (designating 0.05 seconds) is rather arbitrary.  The idea
; is that we'd like any proof to complete, after modification, in at most
; triple the time of the original (and successful) proof -- but a very fast
; time like 0.01 seconds might be a bit random so we give the retry 0.05
; seconds in that case rather than 0.03.  Here is a somewhat relevant archival
; comment from when a step-limit was used instead of a time-limit:

;   Consider what happened with the following book on a 2019 Mac laptop, when
;   using the expression, (+ 1000000 (* 10 steps)).

;   books/workshops/2003/cowles-gamboa-van-baalen_matrix/support/matrix.cert.out
;   Form:  ( DEFTHM ARRAY2P-DETERMINANT-INVERSE-LOOP-A ...)
;   Time:  2571.44 seconds (prove: 2570.36, print: 1.05, other: 0.03)

;   On a slower machine than that laptop, but a normal regression, for that
;   same event, I got this.

;   Time:  9.72 seconds (prove: 9.46, print: 0.25, other: 0.00)

;   Maybe that theorem is unusual: 18 hypotheses.  On the other hand, at least
;   18 runes is probably not at all unusual, and we might start dealing with
;   runes again in the future.  So I'll use the expression used by remove-hyps,
;   (+ 1000 (* 3 steps)).  5/21/2022: Maybe now that we no longer remove one
;   rune at a time we can use a bigger time-limit, but let's not mess with the
;   success of previous runs and remove-hyps.

  (declare (xargs :guard (or (null time)
                             (rationalp time))))
  (and time
       (+ 1/20 (* 3 time))))

(set-evisc-tuple t :sites :gag-mode) ; suppress some printing

; Keep the following in sync with the same form in the following files.
; customize.lsp
; customize-laptop.lsp
; tests/customize-tests.lsp
(let ((adv (getenv$-raw "ACL2_ADVICE")))
  (when (and adv (not (equal adv "")))
    (pushnew :skip-hyp *features*)
    (pushnew :skip-book-runes *features*)
    (pushnew :skip-rune *features*)
    (pushnew :acl2-advice *features*)))

(defrec acl2data
; WARNING: Keep this the same as this record definition in count-acl2data.lisp.
  ((hyp-alist hint-setting-alist . book-runes-alist)
   ((hash expansion-stack goal . goal-clauses) event . rule-classes)
   (used-induction . rune-alist)
   . symbol-table)
  nil)

(assign acl2data-entry nil)
(assign acl2data-alist nil)

(assign my-augmented-disabled-runes nil)

(defvar *expansion-stack* nil) ; always nil at the top level

(defvar *acl2data-prove-time* 0)

(defun prove-set-time (term pspv hints ens wrld ctx state)
  (let ((time1 (get-internal-run-time)))
    (er-let* ((ttree (prove term pspv hints ens wrld ctx state)))
      (progn (setq *acl2data-prove-time*
                   (/ (- (get-internal-run-time) time1)
                      internal-time-units-per-second))
             (value ttree)))))

(defun induction-free-ttree (ttree)

; This can probably be made much more efficient, but the cost is probably
; trivial so let's not bother.

  (not (assoc-eq :induction (all-runes-in-ttree ttree nil))))

(defun skip-retry (kwd state)

; Kwd is from (defrec acl2data ...), omitting the "-alist" suffix.

; Our use of skip-retry is, in a sense, very inefficient, in that we compute
; pair below repeatedly for a given book that's skipped for retries (one
; represented in (f-get-global 'skip-retry-alist state)) rather than figuring
; that out just once per book.  But this computation seems very cheap relative
; to what else is going on (especially, proof attempts), and we avoid writing
; out a __acl2data.out file when maybe-write-bookdata encounters an empty
; alist, which will be the case when the book is skipped for retries.

  (and (f-boundp-global 'skip-retry-alist state)
       (let ((info (f-get-global 'certify-book-info state)))
         (and info
              (let ((pair
                     (assoc-equal
                      (access certify-book-info info :full-book-name)
                      (f-get-global 'skip-retry-alist state))))
                (and pair
                     (or (and (eq :fail (cadr pair))
                              (er hard! 'acl2data
                                  "This book was marked as one whose ~
                                   certification should fail (quickly)."))
                         (null (cdr pair)) ; skip all
                         (member-eq kwd (cdr pair)))))))))

(defmacro note-retries (kwd form)

; Kwd is from (defrec acl2data ...), omitting the "-alist" suffix.  Returns
; (value nil) if we are to skip form.

  `(if (skip-retry ,kwd state)
       (value nil)
     (progn
       (format t "Start retries: ~s.~%" ,kwd)
       ,form)))

(defun acl2data-clausify+ (term state)
  (let* ((wrld (w state))
         (term (expand-some-non-rec-fns '(implies) term wrld))
         (term (remove-guard-holders term wrld)))
    (clausify term nil t (sr-limit wrld))))

(defun acl2data-load (x)
  (load (concatenate 'string
                     (f-get-global 'connected-book-directory *the-live-state*)
                     x)))

(acl2data-load "patch-type-set-b.lsp")
(acl2data-load "patch-induct-2.lsp")
(acl2data-load "patch-defthm.lsp")
(acl2data-load "patch-history-management.lsp")
(acl2data-load "patch-other-events-1.lsp")
(acl2data-load "patch-other-events-2.lsp")
(acl2data-load "patch-other-events-3.lsp")
(acl2data-load "patch-other-events-4.lsp")

(defun format-acl2data-alist (acl2data-alist acc)

; Acl2data-alist is an alist with entries (event-name . acl2data), where
; acl2data is an acl2data record.  We accumulate into acc the result of
; replacing each acl2data record with a list of the following form.

;   ((:hyp-alist (hyp1 ..) (hyp2 ..) ...)
;    (:hint-setting-alist (hs1 ..) (hs2 ..) ...)
;    (:book-runes-alist (book1 ..) (book2 ..) ...)
;    (:rune-alist (rune1 ..) (rune2 ..) ...)
;    )

; Of course, this reverses acl2data-alist, which is fine since it was
; presumably created by pushing entries onto the front.

  (cond
   ((endp acl2data-alist) acc)
   (t (format-acl2data-alist
       (cdr acl2data-alist)
       (acons (caar acl2data-alist)
              (let* ((pair (car acl2data-alist))
                     (rec (cdr pair))
                     (hash (access acl2data rec :hash))
                     (expansion-stack (access acl2data rec :expansion-stack))
                     (goal (access acl2data rec :goal))
                     (goal-clauses (access acl2data rec :goal-clauses))
                     (event (access acl2data rec :event))
                     (rule-classes (access acl2data rec :rule-classes))
                     (used-induction (access acl2data rec :used-induction))
                     #-skip-hyp
                     (hyp-alist (access acl2data rec :hyp-alist))
                     #-skip-hint-setting
                     (hint-setting-alist (access acl2data rec
                                                 :hint-setting-alist))
                     #-skip-rune
                     (rune-alist (access acl2data rec :rune-alist))
                     #-skip-book-runes
                     (book-runes-alist (access acl2data rec :book-runes-alist))
                     (symbol-table (access acl2data rec :symbol-table)))
                `((:goal ,goal)
                  (:hash ,hash)
                  (:expansion-stack ,expansion-stack)
                  (:goal-clauses ,goal-clauses)
                  (:event ,event)
                  (:rule-classes ,rule-classes)
                  (:used-induction ,used-induction)
                  #-skip-hyp
                  (:hyp-alist ,hyp-alist)
                  #-skip-hint-setting
                  (:hint-setting-alist ,hint-setting-alist)
                  #-skip-book-runes
                  (:book-runes-alist ,book-runes-alist)
                  #-skip-rune
                  (:rune-alist ,rune-alist)
                  (:symbol-table ,symbol-table)))
              acc)))))

;;; Next we quite thoroughly hijack maybe-write-bookdata.  Rather than putting
;;; the new definition in patch-other-events.lsp, we just copy its original
;;; definition here and check programmatically that the formals haven't
;;; changed.

(assert (equal (formals 'maybe-write-bookdata (w *the-live-state*))
               '(full-book-string full-book-name wrld ctx state)))

#|
(defun maybe-write-bookdata (full-book-string full-book-name wrld ctx state)

; We are given a full-book-string and corresponding full-book-name, say for
; foo.lisp.  Then when state global 'write-bookdata is not :never, and either
; it's also not nil or environment variable ACL2_WRITE_BOOKDATA is non-empty,
; then certification of full-book-name will cause a file foo__bookdata.out to
; be written.  That file will be of the form (full-book-name . kwd-values),
; where kwd-values is a keyword-value-listp that associates keywords with lists
; as follows.  In each case, only events in the world after including the book
; are considered, hence not events that are merely local or events events
; within other books, but including events from the portcullis (certification
; world) for foo.lisp.  The keyword :books is associated with the list of
; full-book-names of included books.  Each other keyword is associated with an
; alist that associates each key, a package name, with a list of symbol-names
; for symbols in that package that are introduced for that keyword, as follows.

; :CONSTS   - constant symbol introduced by defconst
; :FNS      - function symbol: introduced by defun, defuns, or defchoose;
;             or constrained
; :LABELS   - symbol introduced by deflabel
; :MACROS   - macro name introduced by defmacro
; :STOBJS   - stobj name introduced by defstobj or defabsstobj
; :THEORIES - theory name introduced by deftheory
; :THMS     - theorem name introduced by defthm or defaxiom

  (let ((write-bookdata (f-get-global 'write-bookdata state)))
    (cond
     ((eq write-bookdata :never)
      state)
     (t
      (mv-let (erp val state)
        (if write-bookdata
            (value t)
          (getenv! "ACL2_WRITE_BOOKDATA" state))
        (assert$
         (null erp)
         (cond
          (val
           (let ((outfile (concatenate 'string
                                       (remove-lisp-suffix full-book-string t)
                                       "__bookdata.out")))
             (mv-let
               (channel state)
               (open-output-channel outfile :object state)
               (cond ((null channel)
                      (prog2$ (er hard ctx
                                  "Error in maybe-write-bookdata: Unable to ~
                                  open file ~x0 for output."
                                  outfile)
                              state))
                     (t (pprogn
                         (print-object$-fn (cons full-book-name
                                                 (bookdata-alist full-book-name
                                                                 wrld))
                                           nil ; serialize-character
                                           channel
                                           state)
                         (close-output-channel channel state)))))))
          (t state))))))))
|#

(defun maybe-write-bookdata (full-book-string full-book-name wrld ctx state)
; patch file: This has been completely rewritten.  Original definition is just
; above.
  (declare (ignore wrld))
  (let ((acl2data-alist (@ acl2data-alist)))
    (cond
     ((null acl2data-alist) state)
     (t
      (let ((outfile
             (concatenate
              'string
              (subseq full-book-string 0 (- (length full-book-string) 5))
              "__acl2data.out")))
        (mv-let
          (channel state)
          (open-output-channel outfile :character state)
          (cond ((null channel)
                 (prog2$ (er hard ctx
                             "Error in maybe-write-bookdata: Unable to open ~
                              file ~x0 for output."
                             outfile)
                         state))
                (t (mv-let (erp val state)
                     (state-global-let*
                      ((current-package "ACL2"))
                      (pprogn
                       (mv-let
                         (hi-f hi-t hy-f hy-t br-f br-t ru-f ru-t)
                         (count-acl2data-alist acl2data-alist)
                         (fms "~x0 ;failure_count_hints~|~
                           ~x1 ;total_count_hints~|~
                           ~x2 ;failure_count_hypotheses~|~
                           ~x3 ;total_count_hypotheses~|~
                           ~x4 ;failure_count_book_runes~|~
                           ~x5 ;total_count_book_runes~|~
                           ~x6 ;failure_count_single_rune~|~
                           ~x7 ;total_count_single_rune~|~
                           ~X89~|"
                              (list (cons #\0 hi-f)
                                    (cons #\1 hi-t)
                                    (cons #\2 hy-f)
                                    (cons #\3 hy-t)
                                    (cons #\4 br-f)
                                    (cons #\5 br-t)
                                    (cons #\6 ru-f)
                                    (cons #\7 ru-t)
                                    (cons #\8 (cons full-book-name
                                                    (format-acl2data-alist
                                                     (@ acl2data-alist)
                                                     nil)))
                                    (cons #\9 nil))
                              channel state nil))
                       (f-put-global 'acl2data-alist nil state)
                       (value nil)))
                     (declare (ignore erp val))
                     (close-output-channel channel state))))))))))

(defun push-expansion-stack (sym)
  (if (symbolp sym)
      (push sym *expansion-stack*)
      (error "Not a symbol: ~s" sym)))

(defmacro my-rdepth-error (form &optional preprocess-p)
  (declare (ignore preprocess-p))
  `(prog2$ (step-limit-error1 'some-ctx "Call stack error, actually...."
                              (step-limit-start state) "somewhere" state)
           ,form))

; The following patch files are just a hack so that call stack errors cause
; soft errors (as bogus step-limit errors) rather than hard errors.  The only
; changes to the defun forms below are to use the new my-rdepth-error macro in
; place of rdepth-error.  This horrible hack will not only cause call-stack
; violations to be printed as weird step-limit errors saying "Call stack
; error", but it will cause step-limit errors to be printed that way, too.
(acl2data-load "patch-rewrite-1.lsp")
(acl2data-load "patch-rewrite-2.lsp")
(acl2data-load "patch-induct.lsp")

(set-evisc-tuple nil :sites :gag-mode :iprint :same) ; back to normal
