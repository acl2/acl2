; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(include-book "std/strings/top" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/lists/repeat" :dir :system) ; redundant
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "object-representations")
(include-book "grammar-reader" :skip-proofs-okp t)
(include-book "strings")
(include-book "tokenizer")

(defxdoc earley-parser
  :short "Earley parser written in ACL2"
  :long "A general parser that takes three inputs: a grammar, a lexicon
  (perhaps defined with regular expressions), and a string to parse.  This
  parser then returns a parse tree.  The parsing algorithm that implements this
  property happens to be an Earley Parser (EP) for reasons beyond the scope of
  this documentation.

  Earley Parsers are often also called \"Chart parsers\", because the EP
  terminology dictates that every time the next token in a sentence is read,
  that a new chart is created.  Each chart contains a set of \"states\" that
  roughly correspond to rules in the specified grammar that are in different
  states (depending upon what input has already been seen).

  The EP algorithm starts with exactly one chart, with the starting state as
  its only state.  Through prediction (and in later states, scanning and
  completion) more states get added to this initial chart.  At some point a
  part of speech is encountered, which triggers a scan, which causes the
  chart-index to be incremented, and the next set of states that are created
  are added to a new chart.  This continues, where new charts are created and
  states are added to each of those charts.  In a concrete sense, a list of
  charts is just a list of a list of states.

  As of August 2013, the EP book comes with many extra constants and examples.
  We plan to remove these constants in the long-run but have not yet done so.")

;(set-guard-checking :all)

;; (defthm a-lemma
;;  (IMPLIES (and (< (nfix J) (LEN CHART-LIST))
;;                (chart-list-p chart-list))
;;           (CHART-P (NTH J CHART-LIST)))
;;  :hints (("Goal" :in-theory (enable nth chart-list-p))))

;; (local
;;  (defthm lemma
;;    (implies (and (< (nfix j) (len chart-list))
;;                  (chart-list-p chart-list))
;;             (pstate-list-p (chart->pstates (nth j chart-list))))
;;    :hints (("Goal" :in-theory (enable pstate-list-p)))))

;; (local
;;  (defthm throwaway
;;    (implies (chart-list-p x)
;;             (equal (list-fix x)
;;                    x))))

;; (local
;;  (defthm predictor1-admit-lemma-FORMER-B
;;    (implies (and (pstate-p pstate)
;;                  (pstate-list-p pstate-list))
;;             (pstate-list-p (append pstate-list
;;                                    (list pstate))))))

#|
; no longer needed with the new deflist
(local
 (defthm predictor1-admit-lemma-A
   (implies (and (chart-p chart)
                 (< (nfix j) (len chart-list))
                 (chart-list-p chart-list))
            (chart-list-p
             (update-nth j chart chart-list)))))

(local
 (defthm predictor1-admit-lemma-B
   (implies (pstate-list-p x)
            (pstate-list-p (list-fix x)))))
|#

(local
 (defthm predictor1-lemma
   (implies
    (and (string-list-list-p productions)
         (consp productions)
         (true-listp productions)
         (car productions))
    (< 0 (len (car productions))))
   :rule-classes :linear))

(define predictor1 ((productions string-list-list-p)
                    (B stringp)
                    (j natp)
                    (new-pstates pstate-list-p)
                    (chart-list chart-list-p))
  :guard (and (< j (len chart-list))
              ;(< j (len productions))
              )
  :guard-debug t
  :parents (earley-parser)
  ;:guard-hints (("[1]Goal'" :use ((:instance predictor1-lemma-d))
  ;               :in-theory (disable predictor1-lemma-d)))
  :returns (mv (pstates pstate-list-p :hyp :fguard)
               (chart-list chart-list-p :hyp :fguard))
  ;:assert (pstate-list-p chart-list-p)
  (cond ((not (< j (len chart-list)))
         (prog2$ (er hard? 'predictor1
                     "Predictor1 was given an argument for j that is greater ~
                      than the length of chart-list.  ~%J is: ~x0 ~
                      ~%Productions is: ~x1 ~% Chart-list is ~x2"
                     j productions chart-list)
                 (mv (reverse new-pstates) chart-list)))
        ;; ((not (< j (len productions)))
        ;;  (prog2$ (er hard? 'predictor1
        ;;              "Predictor1 was given an argument for j that is greater ~
        ;;               than the length of productions.  ~%J is: ~x0 ~
        ;;               ~%Productions is: ~x1 ~% Chart-list is ~x2"
        ;;              j productions chart-list)
        ;;          (mv (reverse new-pstates) chart-list)))
        ((atom productions)
         (mv (reverse new-pstates) chart-list))
        (t
         (b* ((new-pstate
               (make-pstate :source B
                            :targets (car productions)
                            :dot 0
                            :start-index j
                            :dot-index j))
              ((run-when (> *debug* 2))
               (cw "  predictor attempting to enqueue")
               (pstate->print new-pstate)
               (cw " into chart ~x0~%"  j))
              (chart-list
               (update-nth j
                           (enqueue new-pstate (nth j chart-list))
                           chart-list)))
           (predictor1 (cdr productions)
                       B
                       j
                       (cons new-pstate new-pstates)
                       chart-list)))))

(defmacro assert-type (type-p default-value form)
  `(let ((val ,form))
     (if (,type-p val)
         val
       (prog2$ (er hard? 'assert-type
                   "~x0 is not of type ~x1")
               ,default-value))))


(define predictor ((pstate pstate-p)
                   (chart-list chart-list-p)
                   (grammar grammar-p))
; Predict possible successor states based on the grammar. As a side-effect, add
; these states to the chart that this state belongs to.
  :guard-debug t
; The specification of this guard/precondition below is inconsistent with the
; runtime-error approach I've used later in other definitions.  I leave it for
; now, since if we want to improve the code, we'll want to push the
; runtime-checks into guards.
  :guard (< (pstate->dot-index pstate) (len chart-list))
  :returns (mv (pstate-list pstate-list-p :hyp :fguard)
               (chart-list chart-list-p :hyp :fguard))
  :parents (earley-parser)
  ;:assert (pstate-list-p chart-list-p)
  (let* ((B (next-target pstate))
         (j (pstate->dot-index pstate))
         (productions (grammar-productions B grammar)))
    (predictor1 productions B j nil chart-list)))

(defn terminal-or-nil-p (x)
  (or (null x)
      (terminal-p x)))

(define member-lexicon-equal ((B stringp)
                              (terminals terminal-list-p))
  :returns (terminal terminal-or-nil-p :hyp :fguard) ; useless return lemma
  ;:assert terminal-or-nil-p
  :parents (earley-parser)
  (cond ((atom terminals)
         nil)
        ((equal b (terminal->class (car terminals)))
         (car terminals))
        (t (member-lexicon-equal b (cdr terminals)))))

(defn pstate-or-nil-p (x)
  (or (null x)
      (pstate-p x)))

;; (defthm scanner-lemma-0
;;   (implies (and (pstate-p pstate)
;;                 (word-list-p word-list)
;;                 (chart-list-p chart-list)
;;                 (lexicon-p lexicon))
;;            (pstate-p (b* ((B (next-target pstate))
;;                           (j (pstate->dot-index pstate))
;;                           (word (nth j word-list))
;;                           ((run-when (> *debug* 2))
;;                            (cw "  scanner is considering if ~@0 is a member of " B)
;;                            (cw "the word-class list for ~x0 (= ~x1)~%"
;;                                word
;;                                (lexicon-lookup word lexicon))))
;;                        (make-pstate :source B
;;                                     :targets (list word)
;;                                     :dot 1
;;                                     :start-index j
;;                                     :dot-index (+ j 1))))))

(defthm scanner-lemma-A
  (implies (and (chart-list-p chart-list)
                (pstate-p new-pstate)
                (integerp j)
                (force (< (+ 1 j) (len chart-list)))
                (force (<= 0 (+ 1 j))))
           (chart-p
            (enqueue new-pstate
                     (nth (+ j 1)
                          chart-list)))))
(defthm scanner-lemma-B
  (implies (and (chart-list-p chart-list)
                (pstate-p new-pstate)
                (integerp j)
                (force (< (+ 1 j) (len chart-list)))
                (force (<= 0 (+ 1 j))))
           (chart-list-p (update-nth (+ j 1)
                                   (enqueue new-pstate
                                            (nth (+ j 1)
                                                 chart-list))
                                   chart-list))))

(define scanner ((pstate pstate-p)
                 (word-list word-list-p)
                 (chart-list chart-list-p)
                 (lexicon lexicon-p))
  :otf-flg t
  :guard-debug t
  :returns (mv (pstate pstate-list-p :hyp :fguard) ; was incorrectly pstate-or-nil-p
               (chart-list chart-list-p :hyp :fguard))
  ;:assert (pstate-or-nil-p chart-list-p)
  :parents (earley-parser)
  (b* ((next-target (next-target pstate))
       (start-index (pstate->dot-index pstate))
       (word (string-fix-with-error (nth start-index word-list)))
       ((run-when (> *debug* 2))
        (cw "  scanner is considering if ~@0 is a member of " next-target)
        (cw "the word-class list for ~x0 (= ~x1)~%"
            word
            (lexicon-lookup word lexicon)))
       (new-pstate
        (make-pstate :source next-target
                     :targets (list word)
                     :dot 1
                     :start-index start-index
                     :dot-index (+ start-index 1))))
    (if (member-lexicon-equal next-target (lexicon-lookup word lexicon))
        (b* (((run-when (> *debug* 2))
              (cw "  scanner attempting to enqueue")
              (pstate->print new-pstate)
              (cw " into chart ~x0~%" (+ start-index 1))))
          (mv nil
              (if (< (+ start-index 1) (len chart-list))
                  (update-nth (+ start-index 1)
                              (enqueue new-pstate
                                       (nth (+ start-index 1) ; this is triggering guard
                                            chart-list))
                              chart-list)
                (prog2$ (er hard? 'scanner "Chart-list wasn't long enough")
                        chart-list))))
      (mv nil chart-list))))

(define completer1 ((potential-prev-states pstate-list-p)
                    (new-states pstate-list-p)
                    (pstate pstate-p)
                    (chart-list chart-list-p)
                    (dot-index natp) ; state-dot-index
                    (source stringp)) ; state-source
  :returns (mv (new-pstates pstate-list-p :hyp :fguard)
               (chart-list chart-list-p :hyp :fguard))
  :parents (earley-parser)
  ;:assert (pstate-list-p chart-list-p)
  (if (atom potential-prev-states)
      (mv (reverse new-states) chart-list)
    (b* ((prev-state (car potential-prev-states))
         (a (next-target prev-state))
; If the non-terminals are different, don't need to add this state
         ((when (not (equal a source)))
          (completer1 (cdr potential-prev-states)
                      new-states
                      pstate
                      chart-list
                      dot-index
                      source))
         ((run-when (and ;(equal a source) ; redundant test
                     (> *debug* 3)))
          (cw "    completer found the state: ")
          (pstate->print prev-state)
          (cw " to match")
          (pstate->print pstate)
          (cw "~%"))

         ((when (not (<= (+ 1 (pstate->dot prev-state))
                         (len (pstate->targets prev-state)))))
          (prog2$ (er hard? 'completer1 "Error related to dot and targets")
                  (mv new-states chart-list)))
         ((when (not (<= (PSTATE->START-INDEX prev-state)
                         DOT-INDEX)))
          (prog2$ (er hard? 'completer1 "Error related to start-index and
                                         dot-index")
                  (mv new-states chart-list)))
         ((when (not (< DOT-INDEX (LEN CHART-LIST))))
          (prog2$ (er hard? 'completer1 "Problem with dot-index and
                                         chart-list")
                  (mv new-states chart-list)))
         (new-pstate (make-pstate
                      :source (pstate->source prev-state)
                      :targets (pstate->targets prev-state)
                      :dot (+ (pstate->dot prev-state) 1)
                      :start-index (pstate->start-index prev-state)
                      :dot-index dot-index
                      :history (append (list pstate)
                                             (pstate->history
                                              prev-state))))
         ((run-when (> *debug* 2))
          (cw "  completer attempting to enqueue")
          (pstate->print new-pstate)
          (cw " into chart ~x0~%" dot-index))
         (chart-list (update-nth dot-index
                                 (enqueue new-pstate (nth dot-index chart-list))
                                 chart-list)))
      (completer1 (cdr potential-prev-states)
                  (cons new-pstate new-states)
                  pstate
                  chart-list
                  dot-index
                  source))))

(define completer ((pstate pstate-p)
                   (chart-list chart-list-p))
  :long "Find and return a list of the previous states that expect this states
   category at this dot-index with the dot moved one step forward. Also returns
   a chart-list that contains those states enqueued in the chart-list."
  :returns (mv (pstate-list pstate-list-p :hyp :fguard)
               (chart-list chart-list-p :hyp :fguard))
  ;:assert (pstate-list-p chart-list-p)
  :parents (earley-parser)
  :guard-debug t
  (b* ((source (pstate->source pstate))
       (start-index (pstate->start-index pstate))
       (dot-index (pstate->dot-index pstate))
; potential-prev-states are those states that could potentially be waiting for
; pstate to complete before they can complete.
       ((when (>= start-index (len chart-list)))
        (prog2$ (er hard? 'completer
                    "Start-index not within range of chart-list")
                (mv (list pstate) chart-list)))
       (potential-prev-states (chart->pstates (nth start-index chart-list))))
    (completer1 potential-prev-states nil pstate chart-list dot-index source)))


(define earley-parse400 ((chart chart-p)
                         (state-index natp)
                         (chart-list chart-list-p)
                         (words word-list-p)
                         (lexicon lexicon-p)
                         (grammar grammar-p))
  :returns (mv (pstate-list pstate-list-p :hyp :fguard)
               (chart-list chart-list-p :hyp :fguard))
  ;:assert (pstate-list-p chart-list-p)
  :guard-debug t
  :parents (earley-parser)
  (b* (
       ((when (not (< state-index (len (chart->pstates chart)))))
        (prog2$ (er hard? 'earley-parse400
                    "State-index out of bounds")
                (mv nil nil)))
       (pstate (nth state-index (chart->pstates chart)))
       ((run-when (> *debug* 1))
        (cw "considering state: ")
        (pstate->print pstate)
        (cw "~%next cat of this~@0 state is ~@1~%"
            (if (incomplete-p pstate) " (incomplete)" "")
            (string-fix (next-target pstate))))) ; no error in this case
    (cond ((or
            (and (incomplete-p pstate)
                 (not (member-equal (next-target pstate)
                                    (lexicon->part-of-speech lexicon)))))
           (b* (((run-when (> *debug* 1))
                 (cw "predicting...~%"))
                ((when (not (< (pstate->dot-index pstate) (len chart-list))))
                 (prog2$ (er hard? 'earley-parse400
                             "Dot-index out of bounds")
                         (mv nil nil))))
             (predictor pstate chart-list grammar))) ; (mv pstate chart-list)
          ((and (incomplete-p pstate)
                (member-equal (next-target pstate)
                        (lexicon->part-of-speech lexicon)))
           (if (equal chart (first (last chart-list)))
               ;(prog2$ (break$) (mv nil chart-list))
               (mv nil chart-list)
             (b* (((run-when (> *debug* 1))
                   (cw "scanning...~%")))
               (scanner pstate words chart-list lexicon))))
          (t (b* (((run-when (> *debug* 1))
                   (cw "completing...~%")))
               (completer pstate chart-list))))))

(define earley-parse200 ((chart chart-p)
                         (state-index natp)
                         (chart-list chart-list-p)
                         (words word-list-p)
                         (lexicon lexicon-p)
                         (grammar grammar-p))

; It's rather difficult to prove termination of this function, because the
; number of pstates in chart actually increases with each recursion,
; basically until a fixed point is reached.  These types of fixed point
; arguments are difficult to make, and we don't want to go through the
; trouble at the moment.  To check that the above skip-proofs only skips the
; termination proof, I submitted the expanded defund in program mode, verified
; its termination with a skip-proofs, and then successfully submitted the
; define in logic mode.

  ;:measure (- (length (chart->pstates chart)) state-index)
  :returns (chart-list chart-list-p :hyp :fguard)
  :guard-debug t
  :parents (earley-parser)
  (if (>= state-index (length (chart->pstates chart)))
      chart-list
    (mv-let (pstates-to-add-to-chart chart-list)
      (earley-parse400 chart state-index chart-list words lexicon grammar)
      (earley-parse200
; This call of chart->add-pstate-list is a critical difference between the ACL2
; and CL versions.
       (chart->add-pstate-list pstates-to-add-to-chart chart)
       (1+ state-index) chart-list words lexicon grammar)))
  :prepwork
  ((skip-proofs
   (defthm earley-parse200-termination-obligation
     (IMPLIES
     (< STATE-INDEX
        (LENGTH (CHART->PSTATES CHART)))
     (< (ACL2-COUNT
             (CHART->ADD-PSTATE-LIST
                  (MV-NTH 0
                          (EARLEY-PARSE400 CHART STATE-INDEX
                                           CHART-LIST WORDS LEXICON GRAMMAR))
                  CHART))
        (ACL2-COUNT CHART)))))))

(define earley-parse100 ((chart chart-p)
                         (chart-index natp)
                         (chart-list chart-list-p)
                         (words word-list-p)
                         (lexicon lexicon-p)
                         (grammar grammar-p))
  :returns (chart-list chart-list-p :hyp :fguard)
  ;:assert chart-list-p
  :parents (earley-parser)
  (b* (((run-when (> *debug* 0))
        (cw "~%---- processing chart #~x0, which is as follows ----~%" chart-index))
       ((run-when (> *debug* 0))
        (cw "~x1~%---- end of chart#~x0 ----~%"
            chart-index
            chart))
       ((run-when (> *debug* 4))
        (cw "---- Here's the associated chart-list for chart #~x0 ----~%"
            chart-index
            chart))
       ((run-when (> *debug* 4))
        (cw "~%~x1~%---- End of associated chart-list for chart #~x0 ----~%"
            chart-index
            chart-list))
       (chart-list
        (earley-parse200 chart 0 chart-list words lexicon
                         grammar))
       ((run-when (> *debug* 0))
        (cw "~%")))
    chart-list))

(define earley-parse50 ((chart-list chart-list-p)
                       (chart-index natp)
                       (words word-list-p)
                       (lexicon lexicon-p)
                       (grammar grammar-p)
                       (updated-chart-list chart-list-p))

; We could prove termination of this function, in particular, if we knew that
; the length of chart-list wasn't changing during each recursion.  But, we'd
; have to prove that earley-parse100 provides that property, which would
; require that we prove that property about earley-parse200.  We leave that
; proof for another day.  However we did make sure that the other events in the
; define admit without a skip-proofs (by admitting expanded defund into program
; mode, verifying its termination with a skip-proofs, and then admitting the
; define.

  ;; this measure is correct, we just don't have the supporting lemmas to use
  ;;it.
  ;;:measure (- (len chart-list) chart-index)

  :returns (chart-list chart-list-p :hyp :fguard)
  :parents (earley-parser)

  (cond ( ;(atom chart-list) ; could also test against length
         (>= chart-index (len chart-list))
         updated-chart-list)
        (t
         (let ((updated-chart-list
                (earley-parse100 (nth chart-index chart-list)
                                 chart-index
                                 updated-chart-list
                                 words
                                 lexicon
                                 grammar))
               (updated-chart-index (1+ chart-index)))
           (earley-parse50 updated-chart-list
                           updated-chart-index
                           words
                           lexicon
                           grammar
                           updated-chart-list))))
  :prepwork
  ((skip-proofs
    (defthm earley-parse50-termination-obligation
      (IMPLIES (< CHART-INDEX (LEN CHART-LIST))
         (< (ACL2-COUNT (EARLEY-PARSE100 (NTH CHART-INDEX CHART-LIST)
                                         CHART-INDEX UPDATED-CHART-LIST
                                         WORDS LEXICON GRAMMAR))
            (ACL2-COUNT CHART-LIST)))))))



(define earley-parse25 ((sentence sentence-p)
                        (grammar grammar-p)
                        (lexicon lexicon-p))
  :returns (chart-list chart-list-p :hyp :fguard)
  :parents (earley-parser)
  :guard-hints (("Goal" :in-theory (enable word-list-p)))
  "Convert a string of words into a chart conforming to the grammar."
  (b* ((words (remove-equal "" (str::strtok sentence '(#\Space))))
       ;; Initialize charts, one chart per word in the sentence (plus an extra
       ;; chart that we won't use, in slot 0)
       (chart-list (replicate (1+ (length words)) (make-chart)))
       ;; Start off by enqueuing a dummy state in the first chart
       (chart-list (update-nth 0 (enqueue (make-pstate :source "G"
                                                       :targets '("S")
                                                       :dot 0
                                                       :start-index 0
                                                       :dot-index 0)
                                          (nth 0 chart-list))
                               chart-list)))
    ;; Then for each chart (= one per word)...
    (earley-parse50 chart-list 0 words lexicon grammar chart-list))
  :prepwork
  ((defthm rewrite-word-list-p
     (equal (word-list-p x)
            (string-listp x)))

   (defthm another-dopey-lemma
     (implies (string-listp x)
              (string-listp (remove-equal "" x))))))

(define earley-parse ((sentence sentence-p)
                        (grammar grammar-p)
                        (lexicon lexicon-p))
  :returns (chart-list chart-list-p :hyp :fguard)
  :parents (earley-parser)
  (earley-parse25 (tokenize-string sentence) grammar lexicon))

; Dynamic programming example

(defconsts (*dp-grammar* state)
  (load-bnf-grammar "./examples/dp-grammar.txt" state))

(defconsts (*dp-lexicon* state)
  (load-lexicon "./examples/dp-lexicon.txt" state))

(defconsts (*dp-parse-tree* state)
  (mv-let (grammar state)
    (load-bnf-grammar "./examples/dp-grammar.txt" state)
    (mv-let (lexicon state)
      (load-lexicon "./examples/dp-lexicon.txt" state)
      (mv (earley-parse "mary runs" grammar lexicon)
          state))))

(defconsts *dp-tree-list*
  (chart-list->trees
   (earley-parse "mary runs" *dp-grammar* *dp-lexicon*)))

(assert! (equal *dp-tree-list*
                '(("S" ("noun" "mary") ("verb" "runs")))))


; Dynamic programming example

(defconsts (*dp2-grammar* state)
  (load-bnf-grammar "./examples/dp2-grammar.txt" state))

(defconsts (*dp2-lexicon* state)
  (load-lexicon "./examples/dp2-lexicon.txt" state))

(defconsts (*dp2-parse-tree* state)
  (mv-let (grammar state)
    (load-bnf-grammar "./examples/dp2-grammar.txt" state)
    (mv-let (lexicon state)
      (load-lexicon "./examples/dp2-lexicon.txt" state)
      (mv (earley-parse "john called mary from denver" grammar lexicon)
          state))))

(defconsts *dp2-tree-list*
 (chart-list->trees
  (earley-parse "john called mary from denver" *dp2-grammar* *dp2-lexicon*)))

;(assert! (equal *dp2-tree-list*
;                '(("S" ("noun" "mary") ("verb" "runs")))))


; Common Lisp example without regular expressions

(defconsts (*grammar* state)
  (load-bnf-grammar "./examples/grammar.txt" state))

(defconsts (*lexicon* state)
  (load-lexicon "./examples/lexicon.txt" state))

(defconsts (*parse-tree-one* state)
  (mv-let (grammar state)
    (load-bnf-grammar "./examples/grammar.txt" state)
    (mv-let (lexicon state)
      (load-lexicon "./examples/lexicon.txt" state)
      (mv (earley-parse "book that flight" grammar lexicon)
          state))))

(defconsts *parse-tree-two*
  (earley-parse "book that flight" *grammar* *lexicon*))

(assert! (equal *parse-tree-one* *parse-tree-two*))

(defconsts *tree-list*
  (chart-list->trees
   (earley-parse "book that flight" *grammar* *lexicon*)))


(assert! (equal *tree-list*
                '(("S" ("VP" ("verb" "book")
                        ("NP" ("det" "that")
                         ("nominal" ("noun" "flight"))))))))

; ; Common Lisp example with regular expressions

(defconsts (*regex-grammar* state)
  (load-bnf-grammar "./examples/regex-grammar.txt" state))

(defconsts (*regex-lexicon* state)
  (load-lexicon "./examples/regex-lexicon.txt" state))

(defconsts *regex-tree-list*
  (chart-list->trees
   (earley-parse "book that 787" *regex-grammar* *regex-lexicon*)))

(assert! (equal *regex-tree-list*
                '(("S" ("VP" ("verb" "book")
                        ("NP" ("det" "that")
                         ("nominal" ("integer" "787"))))))))

(defconsts (*oracle-grammar* state)
  (load-bnf-grammar "./examples/oracle-grammar.txt" state))

(defconsts (*oracle-lexicon* state)
  (load-lexicon "./examples/oracle-lexicon.txt" state))

(defconst *simple-java-example-chart-tree-target*
  '(("S"
     ("CompilationUnit"
      ("TypeDeclarationRag"
       ("TypeDeclaration"
        ("ClassOrInterfaceDeclaration"
         ("ModifierRag" ("Modifier" ("PUBLIC" "public")))
         ("ClassDeclaration"
          ("NormalClassDeclaration"
           ("CLASS" "class")
           ("Identifier" ("IDENTIFIER" "helloworld"))
           ("ClassBody"
            ("LBRACK" "{")
            ("ClassBodyDeclarationRag"
             ("ClassBodyDeclaration"
              ("ModifierRag" ("Modifier" ("PUBLIC" "public"))
               ("ModifierRag" ("Modifier" ("STATIC" "static"))))
              ("MemberDecl"
               ("VOID" "void")
               ("Identifier" ("IDENTIFIER" "main"))
               ("VoidMethodDeclaratorRest" ("FormalParameters" ("LPAREN" "(")
                                            ("RPAREN" ")"))
                ("Block" ("LBRACK" "{")
                 ("RBRACK" "}"))))))
            ("RBRACK" "}")))))))))))

(assert!
 (equal (chart-list->trees
         (earley-parse "public class helloworld { public static void main (   ) { } } "
                       *oracle-grammar* *oracle-lexicon*))
        *simple-java-example-chart-tree-target*))

(assert!
 (equal (chart-list->trees
         (earley-parse "public class helloworld { public static void main () {}}"
                       *oracle-grammar* *oracle-lexicon*))
        *simple-java-example-chart-tree-target*))

(assert!
 (equal (chart-list->trees
         (earley-parse "
  public class helloworld {
    public static void main () {

    }
  }"
                       *oracle-grammar* *oracle-lexicon*))
        *simple-java-example-chart-tree-target*))

#|
(trace$ earley-parse earley-parse25 earley-parse50 earley-parse100
        earley-parse200 earley-parse400)


(trace$ read-next-bnf-production read-next-bnf-production1 read-next-bnf-lexeme
        read-next-bnf-lexeme1 inject-expansions! load-bnf-grammar1
        load-bnf-grammar)

(trace$ predictor1 predictor scanner completer1 completer earley-parse400
        earley-parse200 earley-parse100 earley-parse50 earley-parse25
        earley-parse load-lexicon)

(trace$ predictor1 predictor scanner completer1 completer)
|#
