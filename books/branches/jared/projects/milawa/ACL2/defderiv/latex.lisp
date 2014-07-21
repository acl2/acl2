; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "context")
(include-book "latex-magic")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(ACL2::defttag ACL2::open-output-channel!)


(defconst *dd.nl*
  (ACL2::coerce '(#\Newline) 'ACL2::string))

(defmacro dd.cat (&rest strings)
  `(ACL2::concatenate 'ACL2::string ,@strings))

(defun dd.implode (char-list) ;; => string
  (declare (xargs :mode :program))
  (ACL2::coerce char-list 'ACL2::string))

(defun dd.explode (string) ;; => char-list
  (declare (xargs :mode :program))
  (ACL2::coerce string 'ACL2::list))



(defun dd.safe-get-global (x ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (if (ACL2::boundp-global x ACL2::state)
      (ACL2::f-get-global x ACL2::state)
    nil))


;; We provide "persistent output" that can span many events.  We can open a
;; channel with dd.open, and it stays open until we call dd.close or dd.open
;; upon a new channel.

(defun dd.close-fn (ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let ((channel (dd.safe-get-global 'dd.channel ACL2::state)))
    (if channel
        (let ((ACL2::state (ACL2::close-output-channel channel ACL2::state)))
          (ACL2::assign dd.channel nil))
      (ACL2::value :invisible))))

(defmacro dd.close ()
  `(ACL2::progn
    (ACL2::make-event
     (ACL2::mv-let (er val ACL2::state)
                   (dd.close-fn ACL2::state)
                   (declare (ignore er))
                   (ACL2::mv nil (list 'ACL2::value-triple (list 'quote val)) ACL2::state)))))

(defun dd.open-fn (file ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  ;; Close the previous file if one is open
  (ACL2::mv-let (err val ACL2::state)
                (dd.close-fn ACL2::state)
                (declare (ignore err val))
   ;; Open the new file
   (ACL2::mv-let (channel ACL2::state)
                 (ACL2::open-output-channel! (dd.cat "autodoc/" file) :character ACL2::state)
                 (ACL2::assign dd.channel channel))))

(defmacro dd.open (file)
  `(ACL2::progn
    (ACL2::make-event
     (ACL2::mv-let (er val ACL2::state)
                   (dd.open-fn ,file ACL2::state)
                   (declare (ignore er))
                   (ACL2::mv nil (list 'ACL2::value-triple (list 'quote val)) ACL2::state)))))

(defun dd.write-fn (text ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let ((channel (dd.safe-get-global 'dd.channel ACL2::state)))
    (if channel
        (ACL2::princ$ text channel ACL2::state)
      (let ((err (ACL2::cw "Warning [dd.write]: not writing since no channel is open!~%")))
        (declare (ignore err))
        ACL2::state))))

(defmacro dd.write (&rest text)
  `(ACL2::progn
    (ACL2::make-event
     (let ((ACL2::state (dd.write-fn (dd.cat ,@text *dd.nl* *dd.nl*) ACL2::state)))
       (ACL2::mv nil '(ACL2::value-triple '<dd.text>) ACL2::state)))))

(defun dd.section-fn (name ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (dd.write-fn (dd.cat "\\section{" name "}" *dd.nl* *dd.nl*) ACL2::state))

(defmacro dd.section (name)
  `(ACL2::progn
    (ACL2::make-event (let ((ACL2::state (dd.section-fn ,name ACL2::state)))
                        (ACL2::mv nil '(ACL2::value-triple '<dd.section>) ACL2::state)))))

(defun dd.subsection-fn (name ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (dd.write-fn (dd.cat "\\subsection{" name "}" *dd.nl* *dd.nl*) ACL2::state))

(defmacro dd.subsection (name)
  `(ACL2::progn
    (ACL2::make-event (let ((ACL2::state (dd.subsection-fn ,name ACL2::state)))
                        (ACL2::mv nil '(ACL2::value-triple '<dd.subsection>) ACL2::state)))))



(defun dd.aux-latex-metavariable (x subscriptp) ;; => (twips . char-list)
  (declare (xargs :mode :program))
  (if (consp x)
      (let* ((remaining (dd.aux-latex-metavariable (cdr x) (or subscriptp (equal (car x) #\_))))
             (rem-twips (car remaining))
             (rem-text  (cdr remaining)))
        (if (equal (car x) #\_)
            (if subscriptp
                (ACL2::er hard 'dd.aux-latex-metavariable "Found two subscripts in metavariable.~%~x0~%" x)
              (cons rem-twips
                    (cons #\_ (cons #\{ (app rem-text (list #\}))))))
          (let ((car-twips (if subscriptp
                               (dd.mathit-subscript-twips (car x))
                             (dd.mathit-twips (car x)))))
            (cons (+ car-twips rem-twips)
                  (cons (car x) rem-text)))))
    (cons 0 nil)))

(defun dd.latex-term-metavariable (x) ;; => (twips . string)
  (declare (xargs :mode :program))
  (let* ((twips/char-list (dd.aux-latex-metavariable (dd.explode (ACL2::string-downcase (ACL2::symbol-name x))) nil))
         (twips           (car twips/char-list))
         (char-list       (cdr twips/char-list)))
    (cons twips (dd.cat "\\mathit{" (dd.implode char-list) "}"))))

(defun dd.latex-formula-metavariable (x) ;; => (twips . string)
  (declare (xargs :mode :program))
  (let* ((twips/char-list (dd.aux-latex-metavariable (dd.explode (ACL2::string-upcase (ACL2::symbol-name x))) nil))
         (twips      (car twips/char-list))
         (char-list  (cdr twips/char-list)))
    (cons twips (dd.cat "\\mathit{" (dd.implode char-list) "}"))))

(defun dd.latex-object-variable (x) ;; => (twips . string)
  (declare (xargs :mode :program))
  (let ((text (ACL2::string-downcase (ACL2::symbol-name x))))
    (cons (dd.tt-twips (ACL2::length text))
          (dd.cat "\\Token{" text "}"))))

(defun dd.aux-latex-constant (x) ;; => string
  (declare (xargs :mode :program))
  (cond ((natp x)
         (dd.implode (ACL2::explode-atom x 10)))
        ((symbolp x)
         (ACL2::string-downcase (ACL2::symbol-name x)))
        (t
         (dd.cat "(" (dd.aux-latex-constant (car x)) " . " (dd.aux-latex-constant (cdr x)) ")"))))

(defun dd.latex-constant (x) ;; => (twips . string)
  (declare (xargs :mode :program))
  (let* ((value (cond ((logic.constantp x)
                       (logic.unquote x))
                      ((or (equal x t)
                           (equal x nil)
                           (natp x))
                       x)
                      (t
                       (ACL2::er hard 'dd.latex-constant "Bad input ~x0.~%" x))))
         (text (if (or (equal value t)
                       (equal value nil)
                       (natp value))
                   ;; No quote is necessary
                   (dd.aux-latex-constant value)
                 ;; Insert a quote character
                 (dd.cat "'" (dd.aux-latex-constant value)))))
    (cons (dd.tt-twips (ACL2::length text))
          (dd.cat "\\Token{" text "}"))))

(mutual-recursion
 (defun dd.latex-term (x) ;; => (twips . string)
   (declare (xargs :mode :program))
   (cond ((or (equal x t)
              (equal x nil)
              (natp x)
              (logic.constantp x))
          (dd.latex-constant x))
         ((logic.variablep x)
          (dd.latex-object-variable x))
         ((consp x)
          (if (equal (first x) '?)
              (dd.latex-term-metavariable (second x))
            (let ((fn    (ACL2::string-downcase (ACL2::symbol-name (first x)))))
              (if (consp (cdr x))
                  (let* ((args-twips/text (dd.latex-term-list (cdr x)))
                         (args-twips      (car args-twips/text))
                         (args-text       (cdr args-twips/text)))
                    (cons (+ args-twips (dd.tt-twips (+ (ACL2::length fn) 3)))  ;; name, opening space, and two parens
                          (dd.cat "\\Token{(" fn " }" args-text "\\RP")))
                ;; Else there are no args
                (cons (dd.tt-twips (+ (ACL2::length fn) 2))  ;; name and two parens
                      (dd.cat "\\Token{(" fn ")}"))))))
         (t
          (ACL2::er hard 'dd.latex-term "Bad input: ~x0~%" x))))
 (defun dd.latex-term-list (x) ;; => (twips . string)
   (declare (xargs :mode :program))
   (if (consp x)
       (let* ((first-twips/text (dd.latex-term (car x)))
              (first-twips      (car first-twips/text))
              (first-text       (cdr first-twips/text)))
         (if (consp (cdr x))
             (let* ((rest-twips/text (dd.latex-term-list (cdr x)))
                    (rest-twips      (car rest-twips/text))
                    (rest-text       (cdr rest-twips/text)))
               (cons (+ first-twips (+ (dd.tt-twips 1) rest-twips))
                     (dd.cat first-text "\\SP" rest-text)))
           first-twips/text))
     (cons 0 ""))))



;; We're now about to develop our formula layout algorithm.  It's a bit messy.
;; To start, we're going to prepare the formula for layout.  We generate a list
;; of (twips . text) pairs for the subcomponents of the formula.  We eventually
;; need to combine all these pairs into a single string by adding appropriate
;; newlines.
;;
;; To help ourselves out, we also add layout hints, so the resulting list will
;; actually have these pairs and also some numbers.  The numbers indicate our
;; willingness to split the formula at this point in the list.  The depth
;; should be seeded at 1 to begin and is used to encourage splitting on top
;; level formulas instead of interior subformulas.

(defun dd.aux-latex-formula (x depth)
  (declare (xargs :mode :program))
  (cond ((logic.variablep x)
         (list (dd.latex-formula-metavariable x)))
        ((equal (first x) '=)
         (list (dd.latex-term (second x))
               (+ 4 depth)                        ;; we are willing but not eager to split on =
               (cons *dd.equal-width* " = ")
               (dd.latex-term (third x))))
        ((equal (first x) '!=)
         (list (dd.latex-term (second x))
               (+ 4 depth)                        ;; we are willing but not eager to split on !=
               (cons *dd.neq-width* " \\neq ")
               (dd.latex-term (third x))))
        ((equal (first x) '!)
         (cond ((equal (first (second x)) '=)
                ;; Collapse (! (= lhs rhs)) into (!= lhs rhs)
                (dd.aux-latex-formula (list '!= (second (second x)) (third (second x))) depth))
               ((equal (first (second x)) '!)
                ;; Print (! (! A)) as !!A with no extra parens
                (list* (cons *dd.neg-width* " \\neg ")
                       (dd.aux-latex-formula (second x) (+ 3 depth))))
               ((logic.variablep (second x))
                ;; Write !A instead of !(A) for formula metavariables
                (list* (cons *dd.neg-width* " \\neg ")
                       (dd.aux-latex-formula (second x) (+ 3 depth))))
               (t
                ;; Write parens when we have !(a = b) and !(A v B) in parens
                (list* (cons *dd.neg-width* " \\neg ")
                       (cons *dd.paren-width* "(")
                       (app (dd.aux-latex-formula (second x) (+ 3 depth))
                            (list (cons *dd.paren-width* ")")))))))
        ((equal (first x) 'v)
         (if (equal (first (second x)) 'v)
             ;; Put parens when we have (A v B) v C
             (list* (cons *dd.paren-width* "(")
                    (app (dd.aux-latex-formula (second x) (+ 2 depth))
                         (list* (cons *dd.paren-width* ")")
                                depth                                   ;; preferred split point
                                (cons *dd.vee-width* " \\vee ")
                                (dd.aux-latex-formula (third x) (+ 1 depth)))))
           ;; Don't insert parens otherwise
           (app (dd.aux-latex-formula (second x) (+ 2 depth))
                (list* depth                                            ;; preferred split point
                       (cons *dd.vee-width* " \\vee ")
                       (dd.aux-latex-formula (third x) (+ 1 depth))))))
        (t
         (ACL2::er hard 'dd.aux-latex-formula "Invalid formula pattern ~x0~%" x))))



;; Ideally, every formula wants to be laid out on a single line.  We can
;; estimate how much space this would take just by summing up the twips in the
;; list.  Since the car of a natural is zero, the layout hints don't get in the
;; way of the computation.

(defun dd.max-list (x) ;; => nat
  (declare (xargs :mode :program))
  (if (consp x)
      (max (car x)
           (dd.max-list (cdr x)))
    0))

(defun dd.sum-list (x) ;; => nat
  (declare (xargs :mode :program))
  (if (consp x)
      (+ (car x)
         (dd.sum-list (cdr x)))
    0))

(defun dd.latex-formula-desired-width (formula) ;; => twips
  (declare (xargs :mode :program))
  (let ((parse (dd.aux-latex-formula formula 1)))
    (dd.sum-list (strip-firsts parse))))

(defun dd.latex-formulas-max-desired-width (formulas max-length) ;; => twips
  (declare (xargs :mode :program))
  (if (consp formulas)
      (let ((desired-car-width (dd.latex-formula-desired-width (car formulas)))
            (desired-cdr-width (dd.latex-formulas-max-desired-width (cdr formulas) max-length)))
        (min max-length
             (max desired-car-width desired-cdr-width)))
    0))



;; Before we begin our layout algorithm, we need some auxilliary notions of
;; BRICKS, ROWS, and LAYOUTS.
;;
;; BRICKS are formed by extending the (twips . text) pairs above with a badness
;; field, forming tuples of the form (badness twips text).  The badness
;; indicates how unhappy we are to split after this brick, and is already given
;; to us for some of the pairs in the layout hints that were added to the list.
;; All the other bricks get a badness of 100 + whatever the worst badness was
;; anywhere in the list.

(defun dd.brickp (x)
  (declare (xargs :mode :program))
  (and (tuplep 3 x)
       (natp (first x))               ;; badness
       (natp (second x))              ;; twips
       (ACL2::stringp (third x))))    ;; text

(defun dd.brick-listp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (dd.brickp (car x))
           (dd.brick-listp (cdr x)))
    t))

(defun dd.reversed-brick-list-text (bricks acc) ;; => string
  (declare (xargs :mode :program))
  (if (consp bricks)
      (dd.reversed-brick-list-text (cdr bricks)
                                   (dd.cat (third (car bricks)) acc))
    acc))


;; A ROW contains a list of bricks and has its own width and badness.  Its
;; width should be less than the desired width and its badness is equal to the
;; badness of its last brick.  We represent a row as a (badness, width,
;; reversed-bricks) tuple.

(defun dd.rowp (x)
  (declare (xargs :mode :program))
  (and (tuplep 3 x)
       (natp (first x))               ;; badness
       (natp (second x))              ;; twips
       (dd.brick-listp (third x))))   ;; reversed-bricks

(defun dd.row-text (row) ;; => string
  (declare (xargs :mode :program))
  (dd.reversed-brick-list-text (third row) nil))


;; A LAYOUT is just a list of rows.  The badness of a layout is the sum of the
;; badnesses of each of its rows.  We think of each row in the layout as being
;; separated by a newline character.

(defun dd.layoutp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (dd.rowp (car x))
           (dd.layoutp (cdr x)))
    t))

(defun dd.layout-listp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (dd.layoutp (car x))
           (dd.layout-listp (cdr x)))
    t))

(defun dd.layout-badness (layout) ;; => nat
  (declare (xargs :mode :program))
  (if (consp layout)
      (let* ((row         (first layout))
             (row-badness (first row)))
        (+ row-badness (dd.layout-badness (cdr layout))))
    0))

(defun dd.minimal-layout (layouts best-so-far) ;; => layout
  (declare (xargs :mode :program))
  (if (consp layouts)
      (if best-so-far
          (let ((my-badness   (dd.layout-badness (car layouts)))
                (best-badness (dd.layout-badness best-so-far)))
            (if (< best-badness my-badness)
                (dd.minimal-layout (cdr layouts) best-so-far)
              (dd.minimal-layout (cdr layouts) (car layouts))))
        (dd.minimal-layout (cdr layouts) (car layouts)))
    best-so-far))

(defun dd.layout-text (layout) ;; => string
  (declare (xargs :mode :program))
  (if (consp layout)
      (dd.cat (dd.row-text (car layout))
              (if (consp (cdr layout))
                  (dd.cat " \\\\ " *dd.nl*)
                "")
              (dd.layout-text (cdr layout)))
    nil))



;; We merge our funny combined list of (twips . text) pairs and layout hints
;; into bricks.

(defun dd.aux-merge-into-bricks (x max-badness) ;; => brick list
  (declare (xargs :mode :program))
  (if (consp x)
      (cond ((natp (first x))
             (ACL2::er hard 'dd.aux-merge-into-bricks "Don't expect a number to come first.~%"))
            ((natp (second x))
             (cons (list (second x) ;; score for this brick
                         (car (car x)) ;; twips
                         (cdr (car x))) ;; text
                   (dd.aux-merge-into-bricks (cdr (cdr x)) max-badness)))
            (t
             (cons (list max-badness ;; default score
                         (car (car x)) ;; twips
                         (cdr (car x))) ;; text
                   (dd.aux-merge-into-bricks (cdr x) max-badness))))
    nil))

(defun dd.merge-into-bricks (x) ;; => brick list
  (declare (xargs :mode :program))
  (dd.aux-merge-into-bricks x (+ 100 (dd.max-list x))))



;; The QQUAD BRICK is put into each line of a layout except the first.  This
;; ensures that all lines after the first are indented.

(defconst *dd.qquad-brick*
  (list 0 *dd.qquad-width* " {\\qquad} "))


;; LAYOUT ALGORITHM.
;;
;; Our layout algorithm takes a list of bricks to process, a maximum length to
;; lay out the bricks in, and a list of layouts that contain the bricks we've
;; seen so far.
;;
;; Our algorithm's main operation is to expand upon the list of layouts by
;; adding the next brick to each of them.  There are two ways we can add a
;; brick to a layout:
;;
;;   (1) If it fits within the maximum length we can add it to the current row,
;;   (2) Alternately, we can always put it on a new row.
;;
;; Given N input layouts, this produces up to 2*N output layouts per brick.
;; So, repeating by M bricks, this algorithm is O(2^M) which is terrible.  In
;; practice it is too expensive to apply to even modestly sized formulas, so
;; as a heuristic we only try to start a new row if the badness of the brick
;; is under 100.

(defun dd.split-solutions (max-width brick todo acc) ;; => layout list
  (declare (xargs :mode :program))
  (if (consp todo)
      (let* ((solution1  (car todo))
             (final-row  (car solution1))
             (prev-brick (car (third final-row)))
             ;; Try adding the brick to the current row.
             (new-width (+ (second final-row) (second brick)))  ;; row's width + brick width
             (new-acc   (if (<= new-width max-width)
                            ;; It fits so we add it.
                            (let* ((new-row  (list (first brick) new-width (cons brick (third final-row))))
                                   (new-soln (cons new-row (cdr solution1))))
                              (cons new-soln acc))
                          ;; It doesn't fit so we continue.
                          acc)))
        (if (and (<= 100 (first prev-brick))
                 (<= new-width max-width))
            ;; Heuristic: the previous brick's badness was over 100 so we probably don't
            ;; want to split after it.  Furthermore, this brick fits.  So, don't even try
            ;; to make a new row.
            (dd.split-solutions max-width brick (cdr todo) new-acc)
          ;; Try creating a new row for the new brick.
          (let ((new-width (+ *dd.qquad-width* (second brick)))) ;; width of brick1 + a qquad
            (if (<= new-width max-width)
                (let* ((new-row  (list (first brick) new-width (list brick *dd.qquad-brick*)))
                       (new-soln (cons new-row solution1)))
                  (dd.split-solutions max-width brick (cdr todo) (cons new-soln new-acc)))
              ;; It doesn't even fit on a brand new row.
              (ACL2::er hard 'dd.generate-possible-layouts "Brick ~x0 is too wide.~%" brick)))))
    acc))

(defun dd.generate-layouts (max-width bricks solutions) ;; => layout list
  (declare (xargs :mode :program))
  (if (consp bricks)
      (dd.generate-layouts max-width
                           (cdr bricks)
                           ;; Split all the existing solutions with the first brick
                           (dd.split-solutions max-width (car bricks) solutions nil))
    solutions))

(defun dd.latex-formula (formula max-width) ;; => string
  (declare (xargs :mode :program))
  (let* ((bricks              (dd.merge-into-bricks (dd.aux-latex-formula formula 1)))
         ;; The initial solution will have a single row and a single brick.  We don't add
         ;; a qquad brick becuase it's the starting row and we don't want it indented.
         (initial-row         (list (first (car bricks))  ;; brick1's badness
                                    (second (car bricks)) ;; brick1's width
                                    (list (car bricks)))) ;; brick1 itself
         (initial-soln        (list initial-row))
         ;; Generate the possible layouts then choose a minimal one.
         (possible-layouts    (dd.generate-layouts max-width (cdr bricks) (list initial-soln)))
         (best-layout         (dd.minimal-layout possible-layouts nil)))
    ;; We generated the layouts in reverse, so we have to reverse the text.
    (dd.layout-text (fast-rev best-layout))))

(defconst *dd.formula-padding* 600)
(defconst *dd.overestimate-padding* 1800)

(defun dd.aux-latex-autobox-formulas (formulas twips) ;; => string list
  (declare (xargs :mode :program))
  (if (consp formulas)
      (cons (dd.cat "\\parbox[t]"
                    "{" (dd.twips-to-inches twips) "}"
                    "{$" (dd.latex-formula (car formulas) (- twips *dd.formula-padding*)) "$}")
            (dd.aux-latex-autobox-formulas (cdr formulas) twips))
    nil))

(defun dd.latex-autobox-formulas (formulas twips) ;; => string list
  (declare (xargs :mode :program))
  (let* ((desired-width (dd.latex-formulas-max-desired-width formulas (- twips *dd.overestimate-padding*)))
         (autobox-width (+ desired-width *dd.overestimate-padding*)))
    (dd.aux-latex-autobox-formulas formulas autobox-width)))

(defun dd.latex-autobox-formula (formula twips) ;; => string
  (declare (xargs :mode :program))
  (car (dd.latex-autobox-formulas (list formula) twips)))


