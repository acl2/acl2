; System Utilities -- Numbered Names
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/fresh-namep" :dir :system)
(include-book "kestrel/std/system/pseudo-event-formp" :dir :system)
(include-book "kestrel/utilities/strings/nondigit-chars" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "system/kestrel" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc numbered-names
  :parents (kestrel-utilities system-utilities-non-built-in)
  :short "Utilities for numbered names."
  :long
  "<p>
   A <i>numbered name</i> is a symbol consisting of four parts, in this order:
   </p>
   <ol>
     <li>
     A non-empty <i>base</i> symbol.
     </li>
     <li>
     A non-empty sequence of non-numeric characters
     that marks the start of the numeric index,
     separating it from the base name.
     This character sequence is global but customizable.
     </li>
     <li>
     One of the following:
     <ul>
       <li>
       A non-empty sequence of numeric decimal digits not starting with 0,
       that forms the <i>numeric index</i>,
       which is a positive integer.
       </li>
       <li>
       A non-empty sequence of non-numeric characters
       that forms a <i>wildcard</i> for the numeric index.
       This character sequence is global but customizable.
       </li>
     </ul>
     </li>
     <li>
     A possibly empty sequence of non-numeric characters
     that marks the end of the numeric index
     and that, together with the character sequence in part 2 above,
     surrounds the numeric index or the wildcard.
     This character sequence is global but customizable.
     </li>
   </ol>
   <p>
   Examples of numbered names are:
   </p>
   <ul>
     <li>
     @('MUL2{14}'), where
     @('MUL2') is the base name,
     @('{') marks the start of the numeric index,
     @('14') is the numeric index, and
     @('}') marks the end of the numeric index.
     </li>
     <li>
     @('SORT{*}'), where
     @('SORT') is the base name,
     @('{') marks the start of the numeric index (wildcard),
     @('*') is the wildcard, and
     @('}') marks the end of the numeric index (wildcard).
     </li>
     <li>
     @('FIND$3'), where
     @('FIND') is the base name,
     @('$') marks the start of the numeric index,
     @('3') is the numeric index,
     and nothing marks the end of the numeric index.
     </li>
   </ul>
   <p>
   Numbered names are useful, for instance,
   to denote subsequent versions of functions
   produced by sequences of transformations,
   e.g. @('foo{1}'), @('foo{2}'), ...
   </p>")

(defxdoc numbered-name-index-start
  :parents (numbered-names)
  :short "Starting marker of the numeric index of numbered names."
  :long
  "<p>
   This is stored in a singleton @(tsee table).
   </p>")

(define numbered-name-index-start-p (x)
  :returns (yes/no booleanp)
  :parents (numbered-name-index-start)
  :short "Recognize admissible starting markers
          of the numeric index of numbered names."
  :long
  "<p>
   Check whether @('x') consists of one or more non-numeric characters.
   </p>"
  (and (stringp x)
       (nondigit-charlist-p (explode x))
       (not (equal x ""))))

(table numbered-name-index-start nil nil
  :guard (and (equal key 'start) ; one key => singleton table
              (numbered-name-index-start-p val)))

(defval *default-numbered-name-index-start*
  :parents (numbered-name-index-start)
  :short "Default starting marker of the numeric index of numbered names."
  "{")

(define get-numbered-name-index-start ((wrld plist-worldp))
  :returns (start "A @(tsee numbered-name-index-start-p).")
  :verify-guards nil
  :parents (numbered-name-index-start)
  :short "Retrieve the current starting marker
          of the numeric index of numbered names."
  :long
  "<p>
   If the starting marker is not set yet, the default is returned.
   </p>"
  (let ((pair (assoc-eq 'start (table-alist 'numbered-name-index-start wrld))))
    (if pair (cdr pair) *default-numbered-name-index-start*)))

;; set to default the first time this form is evaluated,
;; then set to current (i.e. no change) when this form is evaluated again
;; (e.g. when this file is redundantly loaded):
(table numbered-name-index-start
  'start (get-numbered-name-index-start world))

(defsection set-numbered-name-index-start
  :parents (numbered-name-index-start)
  :short "Set the starting marker of the numeric index of numbered names."
  :long
  "<p>
   This macro generates an event to override
   the default, or the previously set value.
   </p>
   @(def set-numbered-name-index-start)"
  (defmacro set-numbered-name-index-start (start)
    `(table numbered-name-index-start 'start ,start)))

(defxdoc numbered-name-index-end
  :parents (numbered-names)
  :short "Ending marker of the numeric index of numbered names."
  :long
  "<p>
   This is stored in a singleton @(tsee table).
   </p>")

(define numbered-name-index-end-p (x)
  :returns (yes/no booleanp)
  :parents (numbered-name-index-end)
  :short "Recognize admissible ending markers
          of the numeric index of numbered names."
  :long
  "<p>
   Check whether @('x') consists of zero or more non-numeric characters.
   </p>"
  (and (stringp x)
       (nondigit-charlist-p (explode x))))

(table numbered-name-index-end nil nil
  :guard (and (equal key 'end) ; one key => singleton table
              (numbered-name-index-end-p val)))

(defval *default-numbered-name-index-end*
  :parents (numbered-name-index-end)
  :short "Default ending marker of the numeric index of numbered names."
  "}")

(define get-numbered-name-index-end ((wrld plist-worldp))
  :returns (end "A @(tsee numbered-name-index-end-p).")
  :verify-guards nil
  :parents (numbered-name-index-end)
  :short "Retrieve the current ending marker
          of the numeric index of numbered names."
  :long
  "<p>
   If the ending marker is not set yet, the default is returned.
   </p>"
  (let ((pair (assoc-eq 'end (table-alist 'numbered-name-index-end wrld))))
    (if pair (cdr pair) *default-numbered-name-index-end*)))

;; set to default the first time this form is evaluated,
;; then set to current (i.e. no change) when this form is evaluated again
;; (e.g. when this file is redundantly loaded):
(table numbered-name-index-end
  'end (get-numbered-name-index-end world))

(defsection set-numbered-name-index-end
  :parents (numbered-name-index-end)
  :short "Set the ending marker of the numeric index of numbered names."
  :long
  "<p>
   This macro generates an event to override
   the default, or the previously set value.
   </p>
   @(def set-numbered-name-index-end)"
  (defmacro set-numbered-name-index-end (end)
    `(table numbered-name-index-end 'end ,end)))

(defxdoc numbered-name-index-wildcard
  :parents (numbered-names)
  :short "Wildcard for the numeric index of numbered names."
  :long
  "<p>
   This is stored in a singleton @(tsee table).
   </p>")

(define numbered-name-index-wildcard-p (x)
  :returns (yes/no booleanp)
  :parents (numbered-name-index-wildcard)
  :short "Recognize admissible wildcards
          for the numeric index of numbered names."
  :long
  "<p>
   Check whether @('x') consists of one or more non-numeric characters.
   </p>"
  (and (stringp x)
       (nondigit-charlist-p (explode x))
       (not (equal x ""))))

(table numbered-name-index-wildcard nil nil
  :guard (and (equal key 'wildcard) ; one key => singleton table
              (numbered-name-index-wildcard-p val)))

(defval *default-numbered-name-index-wildcard*
  :parents (numbered-name-index-wildcard)
  :short "Default wildcard for the numeric index of numbered names."
  "*")

(define get-numbered-name-index-wildcard ((wrld plist-worldp))
  :returns (wildcard "A @(tsee numbered-name-index-wildcard-p).")
  :verify-guards nil
  :parents (numbered-name-index-wildcard)
  :short "Retrieve the current wildcard
          for the numeric index of numbered names."
  :long
  "<p>
   If the wildcard is not set yet, the default is returned.
   </p>"
  (let ((pair
         (assoc-eq 'wildcard (table-alist 'numbered-name-index-wildcard wrld))))
    (if pair (cdr pair) *default-numbered-name-index-wildcard*)))

;; set to default the first time this form is evaluated,
;; then set to current (i.e. no change) when this form is evaluated again
;; (e.g. when this file is redundantly loaded):
(table numbered-name-index-wildcard
  'wildcard (get-numbered-name-index-wildcard world))

(defsection set-numbered-name-index-wildcard
  :parents (numbered-name-index-wildcard)
  :short "Set the wildcard for the numeric index of numbered names."
  :long
  "<p>
   This macro generates an event to override
   the default, or the previously set value.
   </p>
   @(def set-numbered-name-index-wildcard)"
  (defmacro set-numbered-name-index-wildcard (wildcard)
    `(table numbered-name-index-wildcard 'wildcard ,wildcard)))

(define check-numbered-name ((name symbolp) (wrld plist-worldp))
  :returns (mv (yes/no booleanp "@('t') iff @('name') is a numbered name.")
               (base symbolp "Base symbol of @('name'),
                              or @('nil') if @('yes/no') is @('nil').")
               (index maybe-natp "Numeric index of @('name'),
                                  or 0 if it is the wildcard,
                                  or @('nil') if @('yes/no') is @('nil')."))
  :verify-guards nil
  :parents (numbered-names)
  :short "Check if a symbol is a numbered name."
  :long
  "<p>
   If successful, return its base symbol and index (or wildcard).
   </p>"
  (b* ((name-chars (explode (symbol-name name)))
       (index-start-chars (explode (get-numbered-name-index-start wrld)))
       (index-end-chars (explode (get-numbered-name-index-end wrld)))
       (wildcard-chars (explode (get-numbered-name-index-wildcard wrld)))
       (len-of-name-without-end-marker (- (len name-chars)
                                          (len index-end-chars)))
       ((unless (and (> len-of-name-without-end-marker 0)
                     (equal (subseq name-chars
                                    len-of-name-without-end-marker
                                    (len name-chars))
                            index-end-chars)))
        (mv nil nil nil))
       (name-chars-without-end-marker
        (take len-of-name-without-end-marker name-chars))
       (digits-of-index
        (reverse (str::take-leading-dec-digit-chars
                  (reverse name-chars-without-end-marker)))))
    (if digits-of-index
        (b* (((when (eql (car digits-of-index) #\0))
              (mv nil nil nil))
             (index (str::dec-digit-chars-value digits-of-index))
             (name-chars-without-index-and-end-marker
              (take (- (len name-chars-without-end-marker)
                       (len digits-of-index))
                    name-chars-without-end-marker))
             (len-of-base-of-name
              (- (len name-chars-without-index-and-end-marker)
                 (len index-start-chars)))
             ((unless (and
                       (> len-of-base-of-name 0)
                       (equal (subseq
                               name-chars-without-index-and-end-marker
                               len-of-base-of-name
                               (len name-chars-without-index-and-end-marker))
                              index-start-chars)))
              (mv nil nil nil))
             (base-chars (take len-of-base-of-name
                               name-chars-without-index-and-end-marker))
             ((unless base-chars) (mv nil nil nil)))
          (mv t (intern-in-package-of-symbol (implode base-chars) name) index))
      (b* ((len-of-name-without-wildcard-and-end-marker
            (- (len name-chars-without-end-marker)
               (len wildcard-chars)))
           ((unless (and (> len-of-name-without-wildcard-and-end-marker 0)
                         (equal
                          (subseq name-chars-without-end-marker
                                  len-of-name-without-wildcard-and-end-marker
                                  (len name-chars-without-end-marker))
                          wildcard-chars)))
            (mv nil nil nil))
           (name-chars-without-wildcard-and-end-marker
            (take len-of-name-without-wildcard-and-end-marker
                  name-chars-without-end-marker))
           (len-of-base-of-name
            (- (len name-chars-without-wildcard-and-end-marker)
               (len index-start-chars)))
           ((unless (and (> len-of-base-of-name 0)
                         (equal
                          (subseq
                           name-chars-without-wildcard-and-end-marker
                           len-of-base-of-name
                           (len name-chars-without-wildcard-and-end-marker))
                          index-start-chars)))
            (mv nil nil nil))
           (base-chars (take len-of-base-of-name
                             name-chars-without-wildcard-and-end-marker))
           ((unless base-chars) (mv nil nil nil)))
        (mv t (intern-in-package-of-symbol (implode base-chars) name) 0)))))

(define make-numbered-name
  ((base symbolp)
   (index-or-wildcard natp "Positive index, or 0 for the wildcard.")
   (wrld plist-worldp))
  :returns (name symbolp)
  :verify-guards nil
  :parents (numbered-names)
  :short "Construct a numbered name from a base and an index (or wildcard)."
  (b* ((base-chars (explode (symbol-name base)))
       (index-start-chars (explode (get-numbered-name-index-start wrld)))
       (index-end-chars (explode (get-numbered-name-index-end wrld)))
       (index-or-wildcard-chars
        (if (zp index-or-wildcard)
            (explode (get-numbered-name-index-wildcard wrld))
          (str::natchars index-or-wildcard)))
       (name-chars (append base-chars
                           index-start-chars
                           index-or-wildcard-chars
                           index-end-chars)))
    (if (equal (symbol-package-name base) *main-lisp-package-name*)
        (intern (implode name-chars) "ACL2")
      (intern-in-package-of-symbol (implode name-chars) base))))

(define make-numbered-name-list ((bases symbol-listp)
                                 (indices/wildcards nat-listp)
                                 (wrld plist-worldp))
  :guard (= (len bases) (len indices/wildcards))
  :returns (names symbol-listp)
  :verify-guards nil
  :parents (numbered-names)
  :short "Lift @(tsee make-numbered-name) to lists."
  (cond ((endp bases) nil)
        (t (cons (make-numbered-name (car bases)
                                     (car indices/wildcards)
                                     wrld)
                 (make-numbered-name-list (cdr bases)
                                          (cdr indices/wildcards)
                                          wrld))))
  ///
  (defret len-of-make-numbered-name-list
    (equal (len names) (len bases))))

(define set-numbered-name-index
  ((name symbolp) (index posp) (wrld plist-worldp))
  :returns (new-name symbolp)
  :verify-guards nil
  :parents (numbered-names)
  :short "Sets the index of a numbered name."
  :long
  "<p>
   If @('name') is a numbered name with base @('base'),
   return the numbered name with base @('base') and index @('index')
   (i.e. replace the index).
   Otherwise, return the numbered name with base @('name') and index @('index')
   (i.e. add the index).
   </p>"
  (b* (((mv is-numbered-name base &) (check-numbered-name name wrld)))
    (if is-numbered-name
        (make-numbered-name base index wrld)
      (make-numbered-name name index wrld))))

(defxdoc numbered-names-in-use
  :parents (numbered-names)
  :short "Numbered names in use."
  :long
  "<p>
   A @(tsee table) keeps track of the numbered names &ldquo;in use&rdquo;.
   The table must be updated explicitly
   every time a new numbered name is used
   (e.g. introduced into the ACL2 @(see world)).
   </p>
   <p>
   The table maps bases of numbered names
   to non-empty sets (encoded as lists) of positive integers.
   If @('base') is mapped to @('(index1 ... indexN)'),
   it means that the numbered names with base @('base')
   and indices @('index1'), ..., @('indexN') are in use.
   </p>")

(table numbered-names-in-use nil nil
  :guard (and (symbolp key)
              (pos-listp val)
              (no-duplicatesp val)))

(defsection add-numbered-name-in-use
  :parents (numbered-names-in-use)
  :short "Record that a numbered name is in use."
  :long
  "<p>
   This macro generates an event form to add a numbered name
   to the table of numbered names in use.
   If the name is not a numbered name,
   or it is a numbered name with a wildcard,
   tha table is unchanged (via an empty @(tsee progn)).
   </p>
   @(def add-numbered-name-in-use)"

  (define add-numbered-name-in-use-fn ((name symbolp) (wrld plist-worldp))
    :returns (event pseudo-event-formp)
    :verify-guards nil
    (b* (((mv is-numbered-name base index) (check-numbered-name name wrld)))
      (if (and is-numbered-name
               (/= index 0))
          (b* ((table (table-alist 'numbered-names-in-use wrld))
               (current-indices (cdr (assoc-eq base table)))
               (new-indices (add-to-set-eql index current-indices)))
            `(table numbered-names-in-use ',base ',new-indices))
        '(progn))))

  (defmacro add-numbered-name-in-use (name)
    `(make-event (add-numbered-name-in-use-fn ',name (w state)))))

(define max-numbered-name-index-in-use ((base symbolp) (wrld plist-worldp))
  :returns (max-index natp)
  :verify-guards nil
  :parents (numbered-names-in-use)
  :short "Largest index of numbered name in use with a given base."
  :long
  "<p>
   Return the largest positive integer @('i')
   such that the numbered name with base @('base') and index @('i') is in use
   (i.e. it is stored in the table).
   If no numbered name with base @('base') is in use,
   return 0.
   </p>"
  (let* ((tab (table-alist 'numbered-names-in-use wrld))
         (current-indices (cdr (assoc-eq base tab))))
    (max-numbered-name-index-in-use-aux current-indices 0))

  :prepwork
  ((define max-numbered-name-index-in-use-aux ((indices pos-listp)
                                               (current-max-index natp))
     :returns (final-max-index natp)
     (cond ((atom indices) (mbe :logic (nfix current-max-index)
                                :exec current-max-index))
           (t (max-numbered-name-index-in-use-aux
               (cdr indices)
               (max (car indices) current-max-index)))))))

(define resolve-numbered-name-wildcard ((name symbolp) (wrld plist-worldp))
  :returns (resolved-name symbolp)
  :verify-guards nil
  :parents (numbered-names)
  :short "Resolve the wildcard in a numbered name (if any)
          to the largest index in use for the name's base."
  :long
  "<p>
   If @('name') is a numbered name
   with base @('base') and the wildcard as index,
   return the numbered name with base @('base') and index @('i'),
   where @('i') is the result of @(tsee max-numbered-name-index-in-use).
   Otherwise, return @('name').
   </p>"
  (b* (((mv is-numbered-name base index) (check-numbered-name name wrld)))
    (if (and is-numbered-name
             (= index 0))
        (make-numbered-name base
                            (max-numbered-name-index-in-use base wrld)
                            wrld)
      (mbe :logic (symbol-fix name)
           :exec name))))

(define next-numbered-name ((name symbolp) (wrld plist-worldp))
  :returns (new-name "A symbol.")
  :mode :program
  :parents (numbered-names)
  :short "Next numbered name with the same base."
  :long
  "<p>
   If @('name') is a numbered name with base @('base') and index @('i'),
   return the numbered name with base @('base') and index @('j'),
   where @('j') is the smallest integer larger than @('i')
   such that the numbered name with base @('base') and index @('j')
   is not in the ACL2 @(see world).
   If @('name') is a numbered name
   with base @('base') and the wildcard as index,
   the behavior is the same as if this function were called
   on the result of @(tsee resolve-numbered-name-wildcard) on @('name').
   If @('name') is not a numbered name, treat it as if it had numeric index 0,
   i.e. return the numbered name with base @('name') and index @('j'),
   where @('j') is the smallest positive integer
   such that the numbered name with base @('name') and index @('j')
   is not in the ACL2 world.
   </p>
   <p>
   This function is independent from the
   <see topic='@(url global-numbered-name-index)'>global index
   for numbered names</see>.
   </p>"
  (b* (((mv is-numbered-name base index) (check-numbered-name name wrld)))
    (if is-numbered-name
        (let ((next-index (if (= index 0)
                              (next-numbered-name-aux
                               base
                               (1+ (max-numbered-name-index-in-use base wrld))
                               wrld)
                            (next-numbered-name-aux base (1+ index) wrld))))
          (make-numbered-name base next-index wrld))
      (let ((next-index (next-numbered-name-aux name 1 wrld)))
        (make-numbered-name name next-index wrld))))

  :prepwork
  ((define next-numbered-name-aux
     ((base symbolp) (current-index posp) (wrld plist-worldp))
     :returns (final-index "A @(tsee posp).")
     :mode :program
     (let ((name (make-numbered-name base current-index wrld)))
       (if (logical-namep name wrld)
           (next-numbered-name-aux base (1+ current-index) wrld)
         current-index)))))

(define next-fresh-numbered-names ((bases symbol-listp)
                                   (index posp)
                                   (names-to-avoid symbol-listp)
                                   (wrld plist-worldp))
  :returns (mv (names "A @(tsee symbol-listp).")
               (new-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Add to each of the given bases the lowest index,
          starting with the given index,
          such that the resulting names are not already in use."
  (b* ((names (make-numbered-name-list bases (repeat (len bases) index) wrld))
       ((when (and (null (fresh-name-listp-msg-weak names 'function wrld))
                   (not (intersectp-eq names names-to-avoid))))
        (mv names (append names names-to-avoid))))
    (next-fresh-numbered-names bases (1+ index) names-to-avoid wrld)))

(define next-fresh-numbered-name ((base symbolp)
                                  (index posp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv (name "A @(tsee symbolp).")
               (new-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Specialize @(tsee next-fresh-numbered-names) to a single name."
  (b* (((mv names names-to-avoid) (next-fresh-numbered-names (list base)
                                                             index
                                                             names-to-avoid
                                                             wrld)))
    (mv (car names) names-to-avoid)))

(defxdoc global-numbered-name-index
  :parents (numbered-names)
  :short "Global index for numbered names."
  :long
  "<p>
   We maintain a global index for numbered names,
   which is initially 1 and can be incremented by 1 or reset to 1.
   This global index is stored in a @(tsee table).
   </p>
   <p>
   This global index can be used, for instance,
   to support the generation of successive sets of numbered names
   such that the names in each set have the same index
   and the index is incremented from one set to the next set.
   </p>
   <p>
   This global index is not used by @(tsee next-numbered-name),
   which increments the index in a more &ldquo;local&rdquo; way.
   </p>")

(table global-numbered-name-index nil nil
  :guard (and (eq key 'index) ; one key => singleton table
              (posp val)))

(define get-global-numbered-name-index ((wrld plist-worldp))
  :returns (global-index "A @(tsee posp).")
  :verify-guards nil
  :parents (global-numbered-name-index)
  :short "Retrieve the global index for numbered names."
  :long
  "<p>
   If the global index is not set yet, 1 is returned.
   </p>"
  (let ((pair (assoc-eq 'index
                        (table-alist 'global-numbered-name-index wrld))))
    (if pair (cdr pair) 1)))

;; set to 1 the first time this form is evaluated,
;; then set to current (i.e. no change) when this form is evaluated again
;; (e.g. when this file is redundantly loaded):
(table global-numbered-name-index
  'index (get-global-numbered-name-index world))

(defsection increment-global-numbered-name-index
  :parents (global-numbered-name-index)
  :short "Increment by 1 the global index for numbered names."
  :long
  "<p>
   This macro generates an event to increment the index by 1.
   </p>
   @(def increment-global-numbered-name-index)"
  (defmacro increment-global-numbered-name-index ()
    '(table global-numbered-name-index
       'index
       (1+ (get-global-numbered-name-index world)))))

(defsection reset-global-numbered-name-index
  :parents (global-numbered-name-index)
  :short "Reset to 1 the global index for numbered names."
  :long
  "<p>
   This macro generates an event to reset the index to 1.
   </p>
   @(def reset-global-numbered-name-index)"
  (defmacro reset-global-numbered-name-index ()
    '(table global-numbered-name-index 'index 1)))

(define set-numbered-name-index-to-global ((name symbolp) (wrld plist-worldp))
  :returns (new-name symbolp)
  :verify-guards nil
  :parents (numbered-names)
  :short "Sets the index of a numbered name
          to the global index for numbered names."
  :long
  "<p>
   Specialize @(tsee set-numbered-name-index)
   to use the global index for numbered names.
   </p>"
  (set-numbered-name-index name (get-global-numbered-name-index wrld) wrld))
