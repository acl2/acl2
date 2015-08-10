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

(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defalist" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
;(include-book "countereg-gen/top" :dir :system)
(include-book "defprimitive")
(include-book "projects/regex/regex-ui" :dir :system)

;(acl2s-defaults :set testing-enabled t)

(defconst *debug* 4)

(std::deflist string-list-p (x)
  (stringp x)
  :elementp-of-nil nil
  :true-listp t
  :parents (earley-parser))

(defn word-p (x)
  (stringp x))

(defthm word-p-implies-string-p
  (implies (word-p x)
           (stringp x))
  :rule-classes (:rewrite :forward-chaining))

(std::deflist word-list-p (x)
  (word-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents (earley-parser))

(defprimitive sentence (x)
  (stringp x)
  :parents (earley-parser))

;;;; Representation of terminals
;;;;----------------------------
(std::defaggregate terminal
  ((class stringp)
   (gender)
   (word word-p))
  :tag :terminal
  :parents (earley-parser))

(std::deflist terminal-list-p (x)
  (terminal-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents (earley-parser))

;;;; Representation of context-free grammar
;;;;---------------------------------------
(std::deflist string-list-list-p (x)
  (string-list-p x)
  :elementp-of-nil t
  :true-listp t
  :parents (earley-parser))

(std::defalist rule-list-p (x)
  :key (stringp x)
  :val (string-list-list-p x)
  :true-listp t
  :parents (earley-parser))

(std::defaggregate grammar
  ((rules rule-list-p)) ; rules should be treated as a hons alist
  :parents (earley-parser)
  :tag :rules)

(define grammar-productions ((non-terminal stringp "The non-terminal symbol")
                             (grammar grammar-p "The grammar"))
  :returns (productions string-list-list-p :hyp :fguard
                        "Set of possible productions for a given non-terminal")
  :parents (earley-parser)
  ;:assert (string-list-list-p)
  (cdr (hons-get non-terminal (grammar->rules grammar))))

;;;; Representation of dictionary
;;;;-----------------------------
(std::defalist dictionary-p (x)
  :key (stringp x)
  :val (terminal-list-p x)
  :true-listp t
  :parents (earley-parser))

(defthm dictionary-p-is-string-keyed-alist-p
  (implies (dictionary-p x)
           (string-keyed-alist-p x))
  :hints (("Goal" :in-theory (enable string-keyed-alist-p))))

(defthm regex-get-of-dictionary-p-returns-terminal-list-p
  (implies (and (stringp x)
                (dictionary-p dict))
           (terminal-list-p (cdr (regex-get x dict))))
  :hints (("Goal" :in-theory (enable regex-get))))

;;;; Representation of lexicon
;;;;--------------------------
(std::defaggregate lexicon
  ((dictionary dictionary-p) ; dictionary should be treated as a hons alist
   (part-of-speech string-list-p))
  :tag :lexicon
  :parents (earley-parser))

(define lexicon-lookup ((word word-p)
                        (lexicon lexicon-p))
  :returns (ans (terminal-list-p ans)
                "The list of terminals associated with the given word"
                :hyp :fguard)
  :parents (earley-parser)
  ;:assert (terminal-list-p)
  (let ((val (regex-get word (lexicon->dictionary lexicon))))
    (if (consp val)
        (cdr val)
      nil))
  ;(cdr (hons-get word (lexicon->dictionary lexicon)))
  )

;;;; Representation of state
;;;;------------------------
;; (defun pstate-count (pstate-list)
;;   (cond ((atom pstate-list)
;;          0)
;;         (t
;;          (+ 1
;;             (pstate-count (cdr (assoc-equal 'history (cdar pstate-list))))
;;             (pstate-count (cdr pstate-list))))))

(defn string-list-or-string-list-list-p (x)
  (or (string-list-p x)
      (string-list-list-p x)))

(defthm string-list-or-string-list-list-p-helper-lemma-1
  (implies (and (string-list-or-string-list-list-p x)
                (not (string-list-p x)))
           (string-list-list-p x)))

(defthm string-list-or-string-list-list-p-helper-lemma-2
  (implies (and (string-list-or-string-list-list-p x)
                (not (string-list-list-p x)))
           (string-list-p x)))

(encapsulate
 ()
 (local
  (defthm assoc-cdr-terminates-lemma
    (implies (consp x)
             (< (acl2-count (cdr (assoc some-label (cdr x))))
                (acl2-count x)))
    :rule-classes :linear))


 (mutual-recursion
  ;; (DEFUND
  ;;     PSTATE-P (X)
  ;;     (DECLARE (XARGS :GUARD T))
  ;;     (AND (CONSP X)
  ;;          (EQ (CAR X) :PSTATE)
  ;;          (ALISTP (CDR X))
  ;;          (CONSP (CDR X))
  ;;          (LET ((SOURCE (CDR (ASSOC 'SOURCE (CDR X))))
  ;;                (TARGETS (CDR (ASSOC 'TARGETS (CDR X))))
  ;;                (DOT (CDR (ASSOC 'DOT (CDR X))))
  ;;                (START-INDEX (CDR (ASSOC 'START-INDEX (CDR X))))
  ;;                (DOT-INDEX (CDR (ASSOC 'DOT-INDEX (CDR X))))
  ;;                (HISTORY (CDR (ASSOC 'HISTORY (CDR X)))))
  ;;               (DECLARE (IGNORABLE SOURCE TARGETS DOT START-INDEX
  ;;                                   DOT-INDEX HISTORY))
  ;;               (AND (STRINGP SOURCE)
  ;;                    (STRING-LIST-P TARGETS)
  ;;                    (NATP DOT)
  ;;                    (< DOT (LEN TARGETS))
  ;;                    (NATP DOT-INDEX)
  ;;                    (< DOT-INDEX (LEN TARGETS))
  ;;                    (PSTATE-LIST-P HISTORY)))))

 ;; (DEFUND
 ;;   PSTATE-P (X)
 ;;   (DECLARE (XARGS :GUARD T))
 ;;   (AND
 ;;    (OR
 ;;     (AND (CONSP X) (EQ (CAR X) :PSTATE))
 ;;     (WITH-OUTPUT-LOCK
 ;;      (CW
 ;;       "Stuctural check for consp and tag ~
 ;;                                     equality failed.  Tag should be ~x0.  ~
 ;;                                     Failing instance is:~% ~x1~%~%"
 ;;       :PSTATE X)))
 ;;    (OR
 ;;     (AND (ALISTP (CDR X)) (CONSP (CDR X)))
 ;;     (WITH-OUTPUT-LOCK
 ;;      (CW
 ;;       "Structural check for ~x0 failed.  Failing instance ~
 ;;                         is:~% ~x1~%"
 ;;       'PSTATE
 ;;       X)))
 ;;    (LET
 ;;     ((SOURCE (CDR (ASSOC 'SOURCE (CDR X))))
 ;;      (TARGETS (CDR (ASSOC 'TARGETS (CDR X))))
 ;;      (DOT (CDR (ASSOC 'DOT (CDR X))))
 ;;      (START-INDEX (CDR (ASSOC 'START-INDEX (CDR X))))
 ;;      (DOT-INDEX (CDR (ASSOC 'DOT-INDEX (CDR X))))
 ;;      (HISTORY (CDR (ASSOC 'HISTORY (CDR X)))))
 ;;     (DECLARE (IGNORABLE SOURCE TARGETS DOT START-INDEX
 ;;                         DOT-INDEX HISTORY))
 ;;     (AND
 ;;      (OR (STRINGP SOURCE)
 ;;          (WITH-OUTPUT-LOCK (CW "Check ~x0 failed~%"
 ;;                                '(STRINGP SOURCE))))
 ;;      (OR (STRING-LIST-P TARGETS)
 ;;          (WITH-OUTPUT-LOCK (CW "Check ~x0 failed~%"
 ;;                                '(STRING-LIST-P TARGETS))))
 ;;      (OR (NATP DOT)
 ;;          (WITH-OUTPUT-LOCK (CW "Check ~x0 failed~%" '(NATP DOT))))
 ;;      (OR (NATP DOT-INDEX)
 ;;          (WITH-OUTPUT-LOCK (CW "Check ~x0 failed~%"
 ;;                                '(NATP DOT-INDEX))))
 ;;      (OR (PSTATE-LIST-P HISTORY)
 ;;          (WITH-OUTPUT-LOCK (CW "Check ~x0 failed~%"
 ;;                                '(PSTATE-LIST-P HISTORY))))
 ;;      (OR
 ;;       (IMPLIES TARGETS (<= DOT (LEN TARGETS)))
 ;;       (WITH-OUTPUT-LOCK (CW "Check ~x0 failed~%"
 ;;                             '(IMPLIES TARGETS (<= DOT (LEN TARGETS))))))))))


  (DEFUND PSTATE-P (X)
          (DECLARE (XARGS :GUARD T))
          (AND (CONSP X)
               (EQ (CAR X) :PSTATE)
               (ALISTP (CDR X))
               (CONSP (CDR X))
               (LET ((SOURCE (CDR (ASSOC 'SOURCE (CDR X))))
                     (TARGETS (CDR (ASSOC 'TARGETS (CDR X))))
                     (DOT (CDR (ASSOC 'DOT (CDR X))))
                     (START-INDEX (CDR (ASSOC 'START-INDEX (CDR X))))
                     (DOT-INDEX (CDR (ASSOC 'DOT-INDEX (CDR X))))
                     (HISTORY (CDR (ASSOC 'HISTORY (CDR X))))
                     ;(INPUT-LENGTH (CDR (ASSOC 'INPUT-LENGTH (CDR X))))
                     )
                    (DECLARE (IGNORABLE SOURCE TARGETS DOT START-INDEX
                                        DOT-INDEX HISTORY #|INPUT-LENGTH|#))
                    (AND (STRINGP SOURCE)
                         (STRING-LIST-P TARGETS)
                         (NATP DOT)
                         (NATP START-INDEX)
                         (NATP DOT-INDEX)
                         (PSTATE-LIST-P HISTORY)
                         ;(NATP INPUT-LENGTH)
                         (<= START-INDEX DOT-INDEX)
                         (<= DOT (LEN TARGETS))
                         ;; (AND (<= DOT INPUT-LENGTH)
                         ;;      (<= DOT-INDEX INPUT-LENGTH)
                         ;;      (<= START-INDEX INPUT-LENGTH))
                         ))))

  (DEFUND PSTATE-LIST-P (X)
    (DECLARE (XARGS :GUARD T
                    :NORMALIZE NIL
                    :VERIFY-GUARDS T
                    :GUARD-DEBUG NIL
                    :GUARD-HINTS NIL))
    (IF (CONSP X)
        (AND (PSTATE-P (CAR X))
             (PSTATE-LIST-P (CDR X)))
        (NULL X)))
  )
 )

(std::deflist pstate-list-p (x)
  (pstate-p x)
  :elementp-of-nil nil
  :true-listp t
  :already-definedp t
  :parents (earley-parser))


(std::defaggregate pstate
; consider renaming to cstate, short for "Chart state", or "staat", which is
; phoenetically similar to "state"
  :short "A Parser State (pstate)"
  :long "Most parser states are created with a grammar rule in mind.  This is
         because most of the parser states are a result of predictions.  A
         relatively small number of them are created by scanning the input
         text.  As such, the members of a parser state look a lot like parts of
         a grammar rule, with markup for tracking where the current parse is in
         the rule and where this particular instance of the grammar rule sits
         inside the input text sentence."
  ((source stringp
            "The starting symbol for the state's grammar rule.")
   (targets string-list-p
            "The targets for the state's grammar rule.  Consists of a left-hand
             side (lhs) that has already been parsed (seen) and a right-hand side
             (rhs) that remains to be parsed (unseen).")
   (dot natp :rule-classes :type-prescription
            "Indicates where the dot is. Everything to the left of the dot has
             been seen and is called the <tt>lhs</tt> and everything to the
             right of the dot has not yet been seen and is called the
             <tt>rhs</tt>.")
   (start-index natp :rule-classes :type-prescription
                "Position in the input text where this instance of the
                 grammar rule starts.")
   (dot-index natp :rule-classes :type-prescription
              "Dot's position, relative to the start of the sentence.")
   (history pstate-list-p "Find out which previous states led to this
                           state (used for printing a parse tree).")
   ;; (input-length natp :rule-classes :type-prescription
   ;;               "Length of the input text.  Not used in any meaningful way except
   ;;                to help with logical obligations")
   )
  :require (

; Since any pstate is constructed for a given input text, it would be nice to
; include the property that the three natp's of the pstate must be less or
; equal to the length of the input text.

            (limit-of-pstate->dot-index
             (<= start-index dot-index)
             :rule-classes (:linear :rewrite))

            (limit-of-pstate->dot
             (<= dot (len targets))
             :rule-classes (:linear :rewrite))

            ;; (limits-based-on-pstate->input-length
            ;;  (and (<= dot input-length)
            ;;       (<= dot-index input-length)
            ;;       (<= start-index input-length)))
            )

  :already-definedp t
  :parents (earley-parser)
  :tag :pstate)

;; (defthm true-listp-of-pstate->history
;;   (implies (pstate-p x)
;;            (true-listp (pstate->history x)))
;;   :rule-classes :type-prescription)

(in-theory (disable pstate-p pstate-list-p))


;(encapsulate
; ()

 ;; (defthm subseq-hack
 ;;   (implies (stringp str)
 ;;            (equal (len (coerce str 'list))
 ;;                   (length str))))

; (ld "counter-example-gen.lisp")

(defthm string-list-p-implies-true-listp

; TODO: Consider making a type-prescription rule

  (implies (string-list-p x)
           (true-listp x)))

(defthm pstate->targets-is-not-a-string

; Shouldn't really be necessary, but the question comes up a lot because of the
; use of subseq and other functions that can accept either a list or a string.

  (implies (pstate-p x)
           (not (stringp (pstate->targets x))))

  :hints (("Goal" :in-theory (enable pstate-p pstate->targets))))

;(in-theory (enable pstate-targets$INLINE))

#|
(local
 (defthm lemmmamama
   (IMPLIES (FORCE (PSTATE-P X))
            (IMPLIES (PSTATE->TARGETS X)
                     (<= (PSTATE->DOT X)
                        (LEN (PSTATE->TARGETS X)))))))
   :hints (("Goal" :in-theory (enable pstate-p)))))
|#

(define pstate->print ((pstate pstate-p))
  :returns (ans null)
  :guard-debug t
  (let ((source (pstate->source pstate))
        (targets (pstate->targets pstate))
        (dot (nfix (pstate->dot pstate))))
    (cw "#{~@0 -> ~*1 . ~*2 [~x3,~x4]}"
        source
        (if targets
            (list "" "~@*" "~@* " "~@* " (subseq-list targets 0 dot))
          nil)
        (if targets
            (list "" "~@*" "~@* " "~@* " (subseq-list targets dot (len targets)))
          nil)
        (pstate->start-index pstate)
        (pstate->dot-index pstate)))
  :parents (earley-parser))


(define incomplete-p ((pstate pstate-p))
  :short "Determines whether there is anything left of the targets behind the dot."
  :returns (ans booleanp)
  ;:assert booleanp
  :parents (earley-parser)
  (not (equal (pstate->dot pstate) (len (pstate->targets pstate)))))

#|
 (define next-target ((pstate pstate-p))
  :short "Returns the next category of 'state'" ; what is a "category"?
  :returns (category (if category (stringp category) t))
  (let ((targets (pstate->targets pstate))
        (dot (pstate->dot pstate)))
    (if (< dot (len targets))
        (nth dot targets)
      nil)))
|#

(defn string-or-string-list-p (x)
  (or (stringp x)
      (string-list-p x)))

(defthm string-or-string-list-p-helper-lemma-1
  (implies (and (string-or-string-list-p x)
                (not (stringp x)))
           (string-list-p x)))

(defthm string-or-string-list-p-helper-lemma-2
  (implies (and (string-or-string-list-p x)
                (not (string-list-p x)))
           (stringp x)))

(local
 (defthm next-target-lemma-1
   (implies (and (natp n)
                 (< n (len x))
                 (string-list-or-string-list-list-p x))
            (string-or-string-list-p (nth n x)))
   :hints (("Goal" :in-theory (enable string-or-string-list-p)))))

(local
 (defthm next-target-lemma-2
   (implies (and (pstate-p pstate)
                 (not (stringp (nth (pstate->dot pstate)
                                    (pstate->targets pstate))))
                 (< (pstate->dot pstate)
                    (len (pstate->targets pstate))))
            (string-list-p (nth (pstate->dot pstate)
                                (pstate->targets pstate))))))

(define next-target ((pstate pstate-p))
  "Returns the next category of 'state'"
  :returns (cat stringp :hyp :fguard)
  :parents (earley-parser)
  ;:assert (stringp)
  (let ((targets (pstate->targets pstate))
        (dot (pstate->dot pstate)))
    (if (< dot (len targets))
        (nth dot targets)
      ""))) ; was nil once upon a time


;; (skip-proofs ; this is hard to get rid of

;; (mutual-recursion
;;  (defun flatten-pstate-list (pstate-list)
;;    (cond ((atom pstate-list)
;;           nil)
;;          (t
;;           (cons (flatten-pstate (car pstate-list))
;;                 (flatten-pstate-list (cdr pstate-list))))))

;;  (defun flatten-pstate (pstate)
;;    (cond ((atom (pstate->history pstate))
;;           (list pstate))
;;          (t (cons pstate
;;                   (flatten-pstate-list (pstate->history pstate))))))
;;  )

;; (defun pstate-count (pstate-list)
;;   (cond ((atom pstate-list)
;;          0)
;;         (t
;;          (+ 1
;;             (pstate-count (pstate->history (car pstate-list)))
;;             (pstate-count (cdr pstate-list))))))


;;  (defun flatten-pstate-list (pstate-list)
;;   (declare (xargs :measure (acl2-count pstate-list)))
;;   (cond ((atom pstate-list)
;;          nil)
;;         (t
;;          (append (car pstate-list)
;;                  (flatten-pstate-list (pstate->history (car pstate-list)))
;;                  (flatten-pstate-list (cdr pstate-list))))))

(encapsulate
 ()
; (local (in-theory (enable pstate->history$inline)))

 (local
  (defthm pstate->tree-collect-lemma1
    (implies (pstate->history pstate)
             (< (acl2-count (pstate->history pstate))
                (acl2-count pstate)))
    :hints (("Goal" :in-theory (enable pstate->history$inline)))))

;(local (in-theory (disable pstate->history$inline)))

 (local
  (defthm pstate->tree-collect-lemma2
    (implies (and (true-listp x)
                  (atom x))
             (equal (not x) t))))

 (mutual-recursion
  (defun pstate->tree-collect (pstates)
    (declare (xargs :guard (pstate-list-p pstates)
                    :guard-debug t
                    :guard-hints (("Goal" :use ((:instance pstate->tree-collect-lemma2
                                                           (x (pstate->targets pstate))))))))
    (cond ((atom pstates)
           nil)
          (t (cons (pstate->tree (car pstates)) ; need to check collect for whether it removes duplicates)
                   (pstate->tree-collect (cdr pstates))))))

  (defun pstate->tree (pstate)
    "Creates a tree from a chart-listing object containing charts" ; ummmm what? there aren't any charts here
    (declare (xargs :guard (pstate-p pstate)))
    (if (null (pstate->history pstate))
        (list (pstate->source pstate)
              (if (atom (pstate->targets pstate))
                  (er hard? 'pstate->tree
                      "Expected (pstate->targets pstate) to be a consp but pstate ~
                       was ~x0"
                      pstate)
                (car (pstate->targets pstate))))
      (cons (pstate->source pstate)
            (reverse (pstate->tree-collect (pstate->history pstate))))))))

;; (defun pstate-list->tree (pstate-list)
;;   (declare (xargs :guard (pstate-list-p pstate-list)
;;                    ;:measure (acl2-count (flatten-pstate-list pstate-list))
;;                    ))
;;    (cond ((atom pstate-list)
;;           nil)
;;          (t
;;           (append (car pstate-list)
;;                   (pstate-list->tree (pstate->history (car pstate-list)))
;;                   (pstate-list->tree (cdr pstate-list))))))

;; (defun pstate->tree-new (pstate)
;;   "Creates a tree from a chart-listing object containing charts"
;;   (declare (xargs :guard (pstate-p pstate)
;;                   :measure (pstate-count (list pstate))))
;;   (cond ((atom

;;;; Representation of charts
;;;;-------------------------
(std::defaggregate chart
  (pstates)
  :require ((pstate-list-p-of-chart->pstates
             (pstate-list-p pstates)))
  ;:debugp t
  :parents (earley-parser)
  :tag :chart)

;; (defthm true-listp-of-chart->pstates
;;   (implies (chart-p x)
;;            (true-listp (chart->pstates x)))
;;   :rule-classes :type-prescription)

(local
 (defthmd enqueue-hack
   (implies (pstate-list-p pstates)
            (pstate-list-p (list-fix pstates)))))

(define enqueue ((pstate pstate-p)
                 (chart chart-p))
; enqueue should really be rewritten to accept a chart-list and an index to update
  :guard-hints (("Goal" :in-theory (enable list-fix pstate-list-p
                                           enqueue-hack)))
  :parents (earley-parser)
  :returns (chart chart-p :hyp :fguard)
  ;:assert chart-p
  (if (member-equal pstate (chart->pstates chart))
      (if (> *debug* 3)
          (progn$ (cw "  the state ")
                  (pstate->print pstate)
                  (cw "is already in the chart~%")
                  chart)
        chart)
    (change-chart chart
                  :pstates (append (chart->pstates chart)
                                   (list pstate)))))

(define chart->add-pstate-list ((pstate-list pstate-list-p)
                                (chart chart-p))
  :returns (chart chart-p :hyp :fguard)
  :parents (earley-parser)
  ;:assert (chart-p)
  (cond ((atom pstate-list)
         chart)
        (t (chart->add-pstate-list (cdr pstate-list)
                                   (enqueue (car pstate-list)
                                            chart)))))

(defun pstate-list->print (pstate-list)
  (declare (xargs :guard (pstate-list-p pstate-list)))
  (cond ((atom pstate-list)
         nil)
        (t
         (progn$ (pstate->print (car pstate-list))
                 (cw "~%")
                 (pstate-list->print (cdr pstate-list))))))

(defun chart->print (chart)
  (declare (xargs :guard (chart-p chart)))
  (progn$ (cw "#CHART:~%")
          (pstate-list->print (chart->pstates chart))
          (cw "~%")))

;;;; Representation of chart listings
;;;;---------------------------------
(std::deflist chart-list-p (x)
  (chart-p x)
  :elementp-of-nil nil
  :true-listp t
  :parents (earley-parser))

;; (std::defaggregate chart-listing
;;   (charts)
;;   :require ((chart-list-p-of-chart-listing->charts
;;              (chart-list-p charts)))
;;   :tag :chart-listing)

;; (in-theory (enable chart-listing->charts)) ; because we have nice rewrite rules for chart-list-p

(define add-chart ((chart chart-p)
                   (chart-list chart-list-p))
  :returns (chart-list chart-list-p :hyp :fguard)
  :parents (earley-parser)
  (cons chart chart-list))

(defun chart-list->print1 (charts)
  (declare (xargs :guard (chart-list-p charts)))
  (cond ((atom charts)
         nil)
        (t
         (prog2$ (chart->print (car charts))
                 (chart-list->print1 (cdr charts))))))

(defun chart-list->print (charts)
  (declare (xargs :guard (chart-list-p charts)))
  (prog2$ (cw "#CHART-LIST:~%")
          (chart-list->print1 charts)))

(define chart-list->collect ((pstates pstate-list-p)
                             (chart-list chart-list-p))
  :parents (earley-parser)
; Don't yet know really what it returns, partly because it's not used in the example
  (cond ((atom pstates)
         nil)
        (t (let ((pstate (car pstates)))
             (if (and (equal (pstate->source pstate) "S")
                      (equal (pstate->start-index pstate)
                             0)
                      (equal (pstate->dot-index pstate)
                             (- (len chart-list) 1))
                      (not (incomplete-p pstate)))
                 (cons (pstate->tree pstate)
                       (chart-list->collect (cdr pstates)
                                            chart-list))
               (chart-list->collect (cdr pstates)
                                    chart-list))))))

(define chart-list->trees ((chart-list chart-list-p))
  :short "Return a list of trees created by following each successful parse in
          the last chart of <tt>chart-list</tt>"
  :parents (earley-parser)
  (b* ((chart (first (last chart-list)))
       ((when (null chart))
        (er hard? 'chart-list->trees
            "Chart-list was null")))
    (chart-list->collect
     (chart->pstates (first (last chart-list)))
     chart-list)))

