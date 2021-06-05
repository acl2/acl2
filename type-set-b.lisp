; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

;; Historical Comment from Ruben Gamboa:
;; I changed this value from 7 to 10 to make room for the
;; positive-, negative-, and complex-irrationals.

(defconst *number-of-numeric-type-set-bits*
  #+:non-standard-analysis 10
  #-:non-standard-analysis 7)

(defconst *type-set-binary-+-table-list*
  (let ((len (expt 2 *number-of-numeric-type-set-bits*)))
    (cons (list :header
                :dimensions (list len len)
                :maximum-length (1+ (* len len))
                :default *ts-acl2-number*
                :name '*type-set-binary-+-table*)
          (type-set-binary-+-alist (1- len) (1- len) nil))))

(defconst *type-set-binary-+-table*
  (compress2 'type-set-binary-+-table
             *type-set-binary-+-table-list*))

(defconst *type-set-binary-*-table-list*
  (let ((len (expt 2 *number-of-numeric-type-set-bits*)))
    (cons (list :header
                :dimensions (list len len)
                :maximum-length (1+ (* len len))
                :default *ts-acl2-number*
                :name '*type-set-binary-*-table*)
          (type-set-binary-*-alist (1- len) (1- len) nil))))

(defconst *type-set-binary-*-table*
  (compress2 'type-set-binary-*-table
             *type-set-binary-*-table-list*))

;; Historical Comment from Ruben Gamboa:
;; As a consequence of the extra numeric arguments, I had to
;; change this table from 6 to 8, to make room for the positive
;; and negative irrationals.

(defconst *type-set-<-table-list*
  #+:non-standard-analysis
  (cons (list :header
              :dimensions '(256 256)
              :maximum-length (1+ (* 256 256))
              :name '*type-set-<-table*)
        (type-set-<-alist 255 255 nil))
  #-:non-standard-analysis
  (cons (list :header
              :dimensions '(64 64)
              :maximum-length (1+ (* 64 64))
              :name '*type-set-<-table*)
        (type-set-<-alist 63 63 nil))
  )

(defconst *type-set-<-table*
  (compress2 'type-set-<-table
             *type-set-<-table-list*))

; Essay on Enabling, Enabled Structures, and Theories

; The rules used by the system can be "enabled" and "disabled".  In a
; break with Nqthm, this is true even of :COMPOUND-RECOGNIZER rules.
; We develop that code now.  Some of the fundamental concepts here are
; that of "rule names" or "runes" and their associated numeric
; correspondents, numes.  We also explain "mapping pairs," "rule name
; designators", "theories," (both "common theories" and "runic
; theories") and "enabled structures".

(defun assoc-equal-cdr (x alist)

; Like assoc-equal but compares against the cdr of each pair in alist.

  (declare (xargs :mode :logic ; might as well put this into :logic mode
                  :guard (alistp alist)))
  (cond ((endp alist) nil)
        ((equal x (cdar alist)) (car alist))
        (t (assoc-equal-cdr x (cdr alist)))))

(defun runep (x wrld)

; This function returns non-nil iff x is a rune, i.e., a "rule name,"
; in wrld.  When non-nil, the value of this function is the nume of
; the rune x, i.e., the index allocated to this rule name in the
; enabled array.  This function returns nil on fake-runes!  See the
; essay on fake-runes below.

; To clear up the confusion wrought by the proliferation of
; nomenclature surrounding rules and the ways by which one might refer
; to them, I have recently adopted more colorful nomenclature than the
; old "rule name," "rule index," "rule id," etc.  To wit,

; rune (rule name):
; an object that is syntactically of the form (token symb . x), where
; token is one of the rule-class tokens, e.g., :REWRITE, :META, etc.,
; symb is a symbolp with a 'runic-mapping-pairs property, and x is
; either nil or a positive integer that distinguishes this rune from
; others generated from different :rule-classes that share the same
; token and symb.  We say that (token symb . x) is "based" on the
; symbol symb.  Formally, rn is a rune iff it is of the form (& symb
; . &), symb is a symbolp with a non-nil runic-info and rn is in the
; range of the mapping-pairs of that runic-info.  This is just another
; way of saying that the range of the mapping pairs of a symbol is a
; complete list of all of the runes based on that symbol.  Each rule
; in the system has a unique rune that identifies it.  The user may
; thus refer to any rule by its rune.  An ordered list of runes is a
; theory (though we also permit some non-runes in theories presented
; by the user).  Each rune has a status, enabled or disabled, as given
; by an enabled structure.  I like the name "rune" because its
; etymology (from "rule name") is clear and it connotes an object that
; is at once obscure, atomic, and yet clearly understood by the
; scholar.

; nume (the numeric counterpart of a rune):
; a nonnegative integer uniquely associated with a rune.  The nume of
; a rune tells us where in the enabled array we find the status of the
; rune.

; runic mapping pair:
; a pair, (nume . rune), consisting of a rune and its numeric
; counterpart, nume.  The 'runic-mapping-pairs property of a symbol is
; the list of all runic mapping pairs whose runes are based on the
; given symbol.  The 'runic-mapping-pairs value is ordered by
; ascending numes, i.e., the first nume in the list is the least.  The
; primary role of runic mapping pairs is to make it more efficient to
; load a theory (ideally a list of runes) into an enabled structure.
; That process requires that we assemble an ACL2 array, i.e., an alist
; mapping array indices (numes) to their values (runes) in the array.
; We do that by collecting the runic mapping pairs of each rune in the
; theory.  We also use these pairs to sort theories: theories are kept
; in descending nume order to make intersection and union easier.  To
; sort a theory we replace each rune in it by its mapping pair, sort
; the result by descending cars, and then strip out the runes to obtain
; the answer.  More on this when we discuss sort-by-fnume.

; event name:
; The symbol, symb, in a rune (token symb . x), is an event name.
; Some event names are allowed in theories, namely, those that are the
; base symbols of runes.  In such usage, an event name stands for one
; or more runes, depending on what kind of event it names.  For
; example, if APP is the name of a defun'd function, then when APP
; appears in a theory it stands for the rune (:DEFINITION APP).  If
; ASSOC-OF-APP is a lemma name, then when it appears in a theory it
; stands for all the runes based on that name, e.g., if that event
; introduced two rewrite rules and an elim rule, then ASSOC-OF-APP
; would stand for (:REWRITE ASSOC-OF-APP . 1), (:REWRITE ASSOC-OF-APP
; . 2), and (:ELIM ASSOC-OF-APP).  This use of event names allows them
; to be confused with rule names.

; Historical Footnote: In nqthm, the executable-counterpart of the
; function APP actually had a distinct name, *1*APP, and hence we
; established the expectation that one could prevent the use of that
; "rule" while allowing the use of the other.  We now use the runes
; (:DEFINITION APP) and (:EXECUTABLE-COUNTERPART APP) to identify
; those two rules added by a defun event.  In fact, the defun adds a
; third rule, named by the rune (:TYPE-PRESCRIPTION APP).  In fact, we
; were driven to the invention of runes as unique rule names when we
; added type-prescription lemmas.

  (declare (xargs :guard
                  (if (and (consp x)
                           (consp (cdr x))
                           (symbolp (cadr x)))
                      (and (plist-worldp wrld)
                           (alistp (getpropc (cadr x) 'runic-mapping-pairs nil
                                             wrld)))
                    t)))
  (cond ((and (consp x)
              (consp (cdr x))
              (symbolp (cadr x)))
         (car
          (assoc-equal-cdr x
                           (getpropc (cadr x) 'runic-mapping-pairs nil wrld))))
        (t nil)))

; Essay on Fake-Runes

; The system has many built in rules that, for regularity, ought to
; have names and numes but don't because they can never be disabled.
; In addition, we sometimes wish to have a rune-like object we can use
; as a mark, without having to worry about the possibility that a
; genuine rune will come along with the same identity.  Therefore, we
; have invented the notion of "fake-runes."  Fake runes are constants.
; By convention, the constant name is always of the form
; *fake-rune-...* and the value of every fake rune is always
; (:FAKE-RUNE-... nil).  Since no rule class will ever start with the
; words "fake rune" this convention will survive the introduction of
; all conceivable new rule classes.  It is important that fake runes
; be based on the symbol nil.  This way they are assigned the nume
; nil by fnume (below) and will always be considered enabled.  The
; function runep does NOT recognize fake runes.  Fake runes cannot be
; used in theories, etc.

; The fake runes are:

; *fake-rune-for-anonymous-enabled-rule*
; This fake rune is specially recognized by push-lemma and ignored.  Thus, if
; you wish to invent a rule that you don't wish to name or worry will be
; disabled, give the rule this :rune and the :nume nil.

; *fake-rune-for-linear*
; This fake rune is a signal that linear arithmetic was used.

; *fake-rune-for-type-set*
; This fake rune is used by type-set to record that built-in facts about
; primitive functions were used.

; *fake-rune-for-cert-data*
; This fake rune is a signal that information was used that was retrieved from
; either the first pass of an encapsulate or certify-book, or from the
; certificate of a certified book.

; WARNING: If more fake runes are added, deal with them in *fake-rune-alist*.

(defmacro base-symbol (rune)

; The "base symbol" of the rune (:token symbol . x) is symbol.

; Note: The existence of this function and the next one suggest that
; runes are implemented abstractly.  Ooooo... we don't know how runes
; are really laid out.  But this just isn't true.  We use car to get
; the token of a rune and we use cddr to get x, above.  But for some
; reason we defined and began to use base-symbol to get the base
; symbol.  In any case, if the structure of runes is changed, all
; mention of runes will have to be inspected.

  `(cadr ,rune))

(defmacro strip-base-symbols (runes)
  `(strip-cadrs ,runes))

(defun fnume (rune wrld)

; Rune has the shape of a rune.  We return its nume.  Actually, this function
; admits every fake-rune as a "rune" and returns nil on it (by virtue of the
; fact that the base-symbol of a fake rune is nil and hence there are no
; mapping pairs).  This fact may be exploited by functions which have obtained
; a fake rune as the name of some rule and wish to know its nume so they can
; determine if it is enabled.  More generally, this function returns nil if
; rune is not a rune in the given world, wrld.  Nil is treated as an enabled
; nume by enabled-runep but not by active-runep.

  (declare (xargs :guard
                  (and (plist-worldp wrld)
                       (consp rune)
                       (consp (cdr rune))
                       (symbolp (base-symbol rune))
                       (alistp (getpropc (base-symbol rune)
                                         'runic-mapping-pairs nil wrld)))))
  (car
   (assoc-equal-cdr rune
                    (getpropc (base-symbol rune) 'runic-mapping-pairs nil
                              wrld))))

(defun frunic-mapping-pair (rune wrld)

; Rune must be a rune in wrld.  We return its mapping pair.

  (assoc-equal-cdr rune
                   (getpropc (base-symbol rune) 'runic-mapping-pairs nil
                             wrld)))

(defun fn-rune-nume (fn nflg xflg wrld)

; Fn must be a function symbol, not a lambda expression.  We return
; either the rune (nflg = nil) or nume (nflg = t) associated with
; either (:DEFINITION fn) (xflg = nil) or (:EXECUTABLE-COUNTERPART fn)
; (xflg = t).  This function knows the layout of the runic mapping
; pairs by DEFUNS -- indeed, it knows the layout for all function
; symbols whether DEFUNd or not!  See the Essay on the Assignment of
; Runes and Numes by DEFUNS.  If fn is a constrained function we
; return nil for all combinations of the flags.

  (let* ((runic-mapping-pairs
          (getpropc fn 'runic-mapping-pairs nil wrld))
         (pair (if xflg (cadr runic-mapping-pairs) (car runic-mapping-pairs))))
    (if nflg (car pair) (cdr pair))))

(defun definition-runes (fns xflg wrld)
  (cond ((null fns) nil)
        (t (cons (fn-rune-nume (car fns) nil xflg wrld)
                 (definition-runes (cdr fns) xflg wrld)))))

(defun get-next-nume (lst)

; We return the next available nume in lst, which is a cdr of the
; current world.  We scan down lst, looking for the most recently
; stored 'runic-mapping-pairs entry.  Suppose we find it, ((n1 .
; rune1) (n2 . rune2) ... (nk . runek)).  Then the next rune will get
; the nume nk+1, which is also just n1+k, where k is the length of the
; list of mapping pairs.  Note: If we see (name runic-mapping-pairs .
; atm) where atm is an atom, then atm is :acl2-property-unbound or
; nil, and we keep going.  Such tuples appear in part because in
; redefinition the 'runic-mapping-pairs property is "nil'd" out.

  (cond ((null lst)
         #+acl2-metering (meter-maid 'get-next-nume 100)
         0)
        ((and (eq (cadr (car lst)) 'runic-mapping-pairs)
              (consp (cddr (car lst))))
         #+acl2-metering (meter-maid 'get-next-nume 100)
         (+ (car (car (cddr (car lst))))
            (length (cddr (car lst)))))
        (t
         #+acl2-metering (setq meter-maid-cnt (1+ meter-maid-cnt))
         (get-next-nume (cdr lst)))))

; We now formalize the notion of "theory".  We actually use two
; different notions of theory here.  The first, which is formalized by
; the predicate theoryp, is what the user is accustomed to thinking of
; as a theory.  Formally, it is a truelist of rule name designators,
; each of which designates a set of runes.  The second is what we
; call a "runic theory" which is an ordered list of runes, where the
; ordering is by descending numes.  We sometimes refer to theories as
; "common theories" to distinguish them from runic theories.  To every
; common theory there corresponds a runic theory obtained by unioning
; together the runes designated by each element of the common theory.
; We call this the runic theory "corresponding" to the common one.

(defun deref-macro-name-lst (macro-name-lst macro-aliases)
  (cond ((atom macro-name-lst) nil)
        (t (cons (deref-macro-name (car macro-name-lst) macro-aliases)
                 (deref-macro-name-lst (cdr macro-name-lst) macro-aliases)))))

(defconst *abbrev-rune-alist*
  '((:d . :definition)
    (:e . :executable-counterpart)
    (:i . :induction)
    (:r . :rewrite)
    (:t . :type-prescription)))

(defun translate-abbrev-rune (x macro-aliases)
  (declare (xargs :guard (alistp macro-aliases)))
  (let ((kwd (and (consp x)
                  (consp (cdr x))
                  (symbolp (cadr x))
                  (cdr (assoc-eq (car x) *abbrev-rune-alist*)))))
    (cond (kwd (list* kwd
                      (deref-macro-name (cadr x) macro-aliases)
                      (cddr x)))
          (t x))))

(defun rule-name-designatorp (x macro-aliases wrld)

; A rule name designator is an object which denotes a set of runes.  We call
; that set of runes the "runic interpretation" of the designator.  A rune, x,
; is a rule name designator, denoting {x}.  A symbol, x, with a
; 'runic-mapping-pairs property is a designator and denotes either
; {(:DEFINITION x)} or else the entire list of runes in the
; runic-mapping-pairs, depending on whether there is a :DEFINITION rune.  A
; symbol x that is a theory name is a designator and denotes the runic theory
; value.  Finally, a singleton list, (fn), is a designator if fn is a function
; symbol; it designates {(:EXECUTABLE-COUNTERPART fn)}.

; For example, if APP is a function symbol then its runic interpretation is
; {(:DEFINITION APP)}.  If ASSOC-OF-APP is a defthm event with, say, three rule
; classes then its runic interpretation is a set of three runes, one for each
; rule generated.  The idea here is to maintain some consistency with the Nqthm
; way of disabling names.  If the user disables APP then only the symbolic
; definition is disabled, not the executable-counterpart, while if ASSOC-OF-APP
; is disabled, all such rules are disabled.

; When true, we return the symbol on which the set of rune is based.  This
; information, which involves the application of deref-macro-name, can be
; useful to callers; see check-theory-msg1.

; Note: We purposely do not define a function "runic-interpretation" which
; returns runic interpretation of a designator.  The reason is that we would
; have to cons that set up for every designator except theories.  The main
; reason we'd want such a function is to define the runic theory corresponding
; to a common one.  We do that below (in
; convert-theory-to-unordered-mapping-pairs1) and open-code "runic
; interpretation."

  (cond ((symbolp x)
         (let ((x (deref-macro-name x macro-aliases)))
           (cond
            ((getpropc x 'runic-mapping-pairs nil wrld)
             x)
            (t (and (not (eq (getpropc x 'theory t wrld) t))
                    x)))))
        ((and (consp x)
              (null (cdr x))
              (symbolp (car x)))
         (let* ((fn (deref-macro-name (car x) macro-aliases)))
           (and (function-symbolp fn wrld)
                (runep (list :executable-counterpart fn) wrld)
                fn)))
        (t (let ((x (translate-abbrev-rune x macro-aliases)))
             (and (runep x wrld)
                  (base-symbol x))))))

(defun theoryp1 (lst macro-aliases wrld)
  (cond ((atom lst) (null lst))
        ((rule-name-designatorp (car lst) macro-aliases wrld)
         (theoryp1 (cdr lst) macro-aliases wrld))
        (t nil)))

(defun theoryp (lst wrld)

; A (common) theory is a truelist of rule name designators.  It is
; possible to turn a theory into a list of runes (which is, itself, a
; theory).  That conversion is done by coerce-to-runic-theory.

  (theoryp1 lst (macro-aliases wrld) wrld))

; Now we define what a "runic theory" is.

(defun runic-theoryp1 (prev-nume lst wrld)

; We check that lst is an ordered true list of runes in wrld, where
; the ordering is by descending numes.  Prev-nume is the nume of the
; previously seen element of lst (or nil if we are at the top-level).

  (cond ((atom lst) (null lst))
        (t
         (let ((nume (runep (car lst) wrld)))
           (cond ((and nume
                       (or (null prev-nume)
                           (> prev-nume nume)))
                  (runic-theoryp1 nume (cdr lst) wrld))
                 (t nil))))))

(defun runic-theoryp (lst wrld)

; A "runic theory" (wrt wrld) is an ordered truelist of runes (wrt wrld), where
; the ordering is that imposed by the numes of the runes, greatest numes first.
; This function returns t or nil according to whether lst is a runic theory in
; wrld.  Common theories are converted into runic-theories in order to do such
; operations as union and intersection.  Our theory processing functions all
; yield runic-theories.  We can save some time in those functions by checking
; if an input theory is in fact a runic theory: if so, we need not sort it.

  (runic-theoryp1 nil lst wrld))

; When we start manipulating theories, e.g., unioning them together,
; we will actually first convert common theories into runic theories.
; We keep runic theories ordered so it is easier to intersect and
; union them.  However, this raises a slightly technical question,
; namely the inefficiency of repeatedly going to the property lists of
; the basic symbols of the runes to recover (by a search through the
; mapping pairs) the measures by which we compare runes (i.e., the
; numes).  We could order theories lexicographically -- there is no
; reason that theories have to be ordered by nume until it is time to
; load the enabled structure.  We could also obtain the measure of
; each rune and cons the two together into a mapping pair and sort
; that list on the cars.  This would at least save the repeated
; getprops at the cost of copying the list twice (once to pair the
; runes with their numes and once to strip out the final list of
; runes).

; We have compared these three schemes in a slightly simpler setting:
; sorting lists of symbols.  The sample list was the list of all event
; names in the initial world, i.e., every symbol in the initial world
; with an 'absolute-event-number property.  The lexicographic
; comparison was done with string<.  The measure (analogous to the
; nume) was the 'absolute-event-number.  We used exactly the same tail
; recursive merge routine used here, changing only the comparator
; expression.  The version that conses the nume to the rune before
; sorting paid the price of the initial and final copying.  The times
; to sort the 2585 symbols were:

; lexicographic:  1.29 seconds
; getprops:       1.18 seconds
; cars:           0.68 seconds

; We have decided to go the car route.  The argument that it does a
; lot of unnecessary consing is unpersuasive in light of the amount of
; consing done by sorting.  For example right off the bat in sort we
; divide the list into its evens and odds, thus effectively copying
; the entire list.  The point is that as it has always been coded,
; sort produces a lot of garbaged conses, so it is not as though
; copying the list twice is a gross insult to the garbage collector.

; We exhibit some performance measures of our actual theory manipulation
; functions later.  See Essay on Theory Manipulation Performance.

; Consider a runic theory.  We want to "augment" it by consing onto
; every rune its nume.  Common theories cannot be augmented until they
; are converted into runic ones.  Naively, then we want to consider two
; transformations: how to convert a common theory to a runic one, and
; how to augment a runic theory.  It turns out that the first
; transformation is messier than you'd think due to the possibility
; that distinct elements of the common theory designate duplicate
; runes.  More on this later.  But no matter what our final design, we
; need the second capability, since we expect that the theory
; manipulation functions will often be presented with runic theories.
; So we begin by augmentation of runic theories.

; Our goal is simply to replace each rune by its frunic-mapping-pair.
; But frunic-mapping-pair has to go to the property list of the basic
; symbol of the rune and then search through the 'runic-mapping-pairs
; for the pair needed.  But in a runic theory, it will often be the
; case that adjacent runes have the same symbol, e.g., (:REWRITE LEMMA
; . 1), (:REWRITE LEMMA . 2), ...  Furthermore, the second rune will
; occur downstream of the first in the 'runic-mapping-pairs of their
; basic symbol.  So by keeping track of where we found the last
; mapping pair we may be able to find the next one faster.

(defun find-mapping-pairs-tail1 (rune mapping-pairs)

; Rune is a rune and mapping-pairs is some tail of the
; 'runic-mapping-pairs property of its basic symbol.  Furthermore, we
; know that we have not yet passed the pair for rune in mapping-pairs.
; We return the tail of mapping-pairs whose car is the pair for rune.

  (cond ((null mapping-pairs)

; At one time we caused a hard error here, because we expected that this case
; never happens.  However, it can happen upon redefinition, when rune is no
; longer a rune.  Here are two examples.

; Example 1:
;   (defthm my-thm (equal (car (cons x x)) x))
;   (deftheory my-thy (current-theory :here))
;   (redef!)
;   (defthm my-thm (equal (cdr (cons x x)) x)
;     :hints (("Goal" :in-theory (theory 'my-thy))))

; Example 2:
;   (defthm my-thm (equal (car (cons x x)) x))
;   (deftheory my-thy (current-theory :here))
;   (redef!)
;   (defthm my-thm (equal (cdr (cons x x)) x) :rule-classes nil)
;   (in-theory (theory 'my-thy))

; As of October 2017 we believe that this code has been in place for many
; years, and at this point it seems that the value of the hard error is
; outweighed by avoiding presentation to users of this obscure error message.

         nil)
        ((equal rune (cdr (car mapping-pairs))) mapping-pairs)
        (t (find-mapping-pairs-tail1 rune (cdr mapping-pairs)))))

(defun find-mapping-pairs-tail (rune mapping-pairs wrld)

; Rune is a rune and mapping-pairs is some tail of the
; 'runic-mapping-pairs property of some basic symbol -- but not
; necessarily rune's.  If it is rune's then rune has not yet been seen
; among those pairs.  If it is not rune's, then we get rune's from
; world.  In any case, we return a mapping-pairs list whose car is the
; mapping pair for rune.

  (cond ((and mapping-pairs
              (eq (base-symbol rune) (cadr (cdr (car mapping-pairs)))))
         (find-mapping-pairs-tail1 rune mapping-pairs))
        (t (find-mapping-pairs-tail1 rune
                                     (getpropc (base-symbol rune)
                                               'runic-mapping-pairs
                                               nil
                                               wrld)))))

(defun augment-runic-theory1 (lst mapping-pairs wrld ans)

; Lst is a runic theory.  We iteratively accumulate onto ans the
; mapping pair corresponding to each element of lst.  Mapping-pairs is
; the tail of some 'runic-mapping-pairs property and is used to speed
; up the retrieval of the pair for the first rune in lst.  See
; find-mapping-pairs-tail for the requirements on mapping-pairs.  The
; basic idea is that as we cdr through lst we also sweep through
; mapping pairs (they are ordered the same way).  When the rune we get
; from lst is based on the same symbol as the last one, then we find
; its mapping pair in mapping-pairs.  When it is not, we switch our
; attention to the 'runic-mapping-pairs of the new basic symbol.

  (cond
   ((null lst) ans)
   (t (let ((mapping-pairs
             (find-mapping-pairs-tail (car lst) mapping-pairs wrld)))
        (cond
         (mapping-pairs
          (augment-runic-theory1 (cdr lst)
                                 (cdr mapping-pairs)
                                 wrld
                                 (cons (car mapping-pairs) ans)))
         (t
          (augment-runic-theory1 (cdr lst)
                                 mapping-pairs
                                 wrld
                                 ans)))))))

(defun augment-runic-theory (lst wrld)

; We pair each rune in the runic theory lst with its nume, returning an
; augmented runic theory.

  (augment-runic-theory1 (reverse lst) nil wrld nil))

; Ok, so now we know how to augment a runic theory.  How about
; converting common theories to runic ones?  That is harder because of
; the duplication problem.  For example, '(APP APP) is a common
; theory, but the result of replacing each designator by its rune,
; '((:DEFINITION app) (:DEFINITION app)), is not a runic theory!  It
; gets worse.  Two distinct designators might designate the same rune.
; For example, LEMMA might designate a collection of :REWRITE rules
; while (:REWRITE LEMMA . 3) designates one of those same rules.  To
; remove duplicates we actually convert the common theory first to a
; list of (possibly duplicated and probably unordered) mapping pairs
; and then use a bizarre sort routine which removes duplicates.  While
; converting a common theory to a unordered and duplicitous list of
; mapping pairs we simply use frunic-mapping-pair to map from a rune
; to its mapping pair; that is, we don't engage in the clever use of
; tails of the mapping pairs properties because we don't expect to see
; too many runes in a common theory, much less for two successive
; runes to be ordered properly.

(defconst *bad-runic-designator-string*
  "This symbol was expected to be suitable for theory expressions; see :DOC ~
   theories, in particular the discussion of runic designators.  One possible ~
   source of this problem is an attempt to include an uncertified book with a ~
   deftheory event that attempts to use the above symbol in a deftheory event.")

(defun convert-theory-to-unordered-mapping-pairs1 (lst macro-aliases wrld ans)

; Note: another function that deals in runic mapping pairs is
; monitorable-runes-from-mapping-pairs.

; This is the place we give meaning to the "runic interpretation" of a
; rule name designator.  Every element of lst is a rule name
; designator.

  (cond
   ((null lst) ans)
   ((symbolp (car lst))
    (let ((temp (getpropc (deref-macro-name (car lst) macro-aliases)
                          'runic-mapping-pairs nil wrld)))
      (cond
       ((and temp
             (eq (car (cdr (car temp))) :DEFINITION)
             (eq (car (cdr (cadr temp))) :EXECUTABLE-COUNTERPART))
        (convert-theory-to-unordered-mapping-pairs1
         (cdr lst) macro-aliases wrld
         (if (equal (length temp) 4)

; Then we have an :induction rune.  See the Essay on the Assignment of Runes
; and Numes by DEFUNS.

             (cons (car temp) (cons (cadddr temp) ans))
           (cons (car temp) ans))))
       (temp
        (convert-theory-to-unordered-mapping-pairs1
         (cdr lst) macro-aliases wrld (revappend temp ans)))
       (t

; In this case, we know that (car lst) is a theory name.  Its 'theory
; property is the value of the theory name and is a runic theory.  We
; must augment it.  The twisted use of ans below -- passing it into
; the accumulator of the augmenter -- is permitted since we don't care
; about order.

        (convert-theory-to-unordered-mapping-pairs1
         (cdr lst) macro-aliases wrld
         (augment-runic-theory1
          (reverse (getpropc (car lst) 'theory
                             `(:error ,*bad-runic-designator-string*)
                             wrld))
          nil
          wrld
          ans))))))
   ((null (cdr (car lst)))
    (convert-theory-to-unordered-mapping-pairs1
     (cdr lst) macro-aliases wrld
     (cons (cadr (getpropc (deref-macro-name (car (car lst)) macro-aliases)
                           'runic-mapping-pairs
                           `(:error ,*bad-runic-designator-string*)
                           wrld))
           ans)))
   (t (convert-theory-to-unordered-mapping-pairs1
       (cdr lst) macro-aliases wrld
       (cons (frunic-mapping-pair (translate-abbrev-rune (car lst)
                                                         macro-aliases)
                                  wrld)
             ans)))))

(defun convert-theory-to-unordered-mapping-pairs (lst wrld)

; This function maps a common theory into a possibly unordered and/or
; duplicitous list of mapping pairs.

  (convert-theory-to-unordered-mapping-pairs1
   lst (macro-aliases wrld) wrld nil))

; Now we develop a merge sort routine that has four interesting
; properties.  First, it sorts arbitrary lists of pairs, comparing on
; their cars which are assumed to be rationals.  Second, it can be
; told whether to produce an ascending order or a descending order.
; Third, it deletes all but one occurrence of any element with the
; same car as another.  Fourth, its merge routine is tail recursive
; and so can handle very long lists.  (The sort routine is not tail
; recursive, but it cuts the list in half each time and so can handle
; long lists too.)

(defun duplicitous-cons-car (x y)

; This is like (cons x y) in that it adds the element x to the list y,
; except that it does not if the car of x is the car of the first element
; of y.

  (cond ((equal (car x) (caar y)) y)
        (t (cons x y))))

(defun duplicitous-revappend-car (lst ans)

; Like revappend but uses duplicitous-cons-car rather than cons.

  (cond ((null lst) ans)
        (t (duplicitous-revappend-car (cdr lst)
                                      (duplicitous-cons-car (car lst) ans)))))

(defun duplicitous-merge-car (parity lst1 lst2 ans)

; Basic Idea: Lst1 and lst2 must be appropriately ordered lists of
; pairs.  Comparing on the cars of respective pairs, we merge the two
; lists, deleting all but one occurrence of any element with the same
; car as another.

; Terminology: Suppose x is some list of pairs and that the car of
; each pair is a rational.  We say x is a "measured list" because the
; measure of each element is given by the car of the element.  We
; consider two orderings of x.  The "parity t" ordering is that in
; which the cars of x are ascending.  The "parity nil" ordering is
; that in which the cars of x are descending.  E.g., in the parity t
; ordering, the first element of x has the least car and the last
; element of x has the greatest.

; Let lst1 and lst2 be two measured lists.  This function merges lst1
; and lst2 to produce output in the specified parity.  However, it
; assumes that its two main inputs, lst1 and lst2, are ordered in the
; opposite parity.  That is, if we are supposed to produce output that
; is ascending (parity = t) then the input must be descending (parity
; = nil).  This odd requirement allows us to do the merge in a tail
; recursive way, accumulating the answers onto ans.  We do it tail
; recursively because we are often called upon to sort huge lists and
; the naive approach has blown the stack of AKCL.

  (cond ((null lst1) (duplicitous-revappend-car lst2 ans))
        ((null lst2) (duplicitous-revappend-car lst1 ans))
        ((if parity
             (> (car (car lst1)) (car (car lst2)))
             (< (car (car lst1)) (car (car lst2))))
         (duplicitous-merge-car parity (cdr lst1) lst2 (duplicitous-cons-car (car lst1) ans)))
        (t (duplicitous-merge-car parity lst1 (cdr lst2) (duplicitous-cons-car (car lst2) ans)))))

(defun duplicitous-sort-car (parity lst)

; Let lst be a list of runes.  If parity = t, we sort lst so that the
; numes of the resulting list are ascending; if parity = nil, the
; numes of the resulting list are descending.

; Note: This function is neat primarily because the merge function is
; tail recursive.  It is complicated by the entirely extraneous
; requirement that it delete duplicates.  The neat thing is that as it
; descends through lst, cutting it in half each time, it recursively
; orders the parts with the opposite sense of ordering.  That is, to
; sort into ascending order it recursively sorts the two parts into
; descending order, which it achieves by sorting their parts into
; ascending order, etc.

  (cond ((null (cdr lst)) lst)
        (t (duplicitous-merge-car parity
                                  (duplicitous-sort-car (not parity) (evens lst))
                                  (duplicitous-sort-car (not parity) (odds lst))
                                  nil))))

(defun augment-theory (lst wrld)

; See also related function runic-theory.

; Given a (common) theory we convert it into an augmented runic
; theory.  That is, we replace each designator in lst by the
; appropriate runes, pair each rune with its nume, sort the result and
; remove duplications.  In the special case that lst is in fact a
; runic theory -- i.e., is already a properly sorted list of runes --
; we just augment it directly.  We expect this case to occur often.
; The various theory manipulation functions take common theories as
; their inputs but produce runic theories as their outputs.
; Internally, they all operate by augmenting the input theory,
; computing with the augmented theory, and then dropping down to the
; corresponding runic theory at the end with strip-cdrs.  Thus if two
; such functions are nested in a user-typed theory expression, the
; inner one will generally have non-runic user-typed input but will
; produce runic output as input for the next one.  By recognizing
; runic theories as a special case we hope to improve the efficiency
; with which theory expressions are evaluated, by saving the sorting.

  (declare (xargs :guard (theoryp lst wrld)))
  (cond ((runic-theoryp lst wrld)
         (augment-runic-theory lst wrld))
        (t (duplicitous-sort-car
            nil
            (convert-theory-to-unordered-mapping-pairs lst wrld)))))

(defmacro assert$-runic-theoryp (runic-theory-expr wrld)

; Comment out one of the following two definitions.

;;; Faster, without checking:
  (declare (ignore wrld))
  runic-theory-expr

;;; Slower, with checking:
;  `(let ((thy ,runic-theory-expr))
;     (assert$ (runic-theoryp thy ,wrld)
;              thy))
  )

(defun runic-theory (lst wrld)

; Lst is a common theory.  We convert it to a runic theory.

; See also related function augment-theory.

  (cond ((runic-theoryp lst wrld) lst)
        (t (assert$-runic-theoryp
            (strip-cdrs
             (duplicitous-sort-car
              nil
              (convert-theory-to-unordered-mapping-pairs lst wrld)))
            wrld))))

; We now develop the foundations of the concept that a rune is "enabled" in the
; current theory.  In ACL2, the user can get "into" a theory with the in-theory
; event, which is similar in spirit to in-package but selects a theory as the
; "current" theory.  A rune is said to be "enabled" if it is a member of the
; runic theory corresponding to the current (common) theory and is said to be
; "disabled" otherwise.

; Historical Note about Nqthm

; Nqthm had no explicit notion of the current theory.  However, implicitly,
; nqthm contained a current theory and the events ENABLE and DISABLE allowed
; the user to add a name to it or delete a name from it.  The experimental
; xnqthm, mentioned elsewhere in this system, introduced the notion of theories
; and tied them to enabling and disabling, following suggestions and patches
; implemented by Bill Bevier during the Kit proofs (and implemented in
; Pc-Nqthm, and extended in Nqthm-1992).  The ACL2 notion of theory is much
; richer because it allows one to compute the value of theories using functions
; defined within the logic.  (end of note)

; Suppose we have a theory which has been selected as current.  This may be the
; globally current theory, as set by the in-theory event, or it may be a
; locally current theory, as set by the in-theory hint to defthm or defun.  We
; must somehow process the current theory so that we can quickly answer the
; question "is rune enabled?"  We now develop the code for doing that.

; The structure defined below is used as a fast way to represent a theory:

(defrec enabled-structure

; WARNING:  Keep this in sync with enabled-structurep.

  ((index-of-last-enabling . theory-array)
   (array-name . array-length)
   array-name-root . array-name-suffix)
  t)

(defun enabled-structure-p (ens)

; We use this function in the guards of other functions.

  (declare (xargs :guard t))
  (and (weak-enabled-structure-p ens)
       (array1p (access enabled-structure ens
                        :array-name)
                (access enabled-structure ens
                        :theory-array))
       (symbolp (access enabled-structure ens
                        :array-name))
       (signed-byte-p 30 (access enabled-structure ens
                                 :array-length))
       (signed-byte-p 30 (access enabled-structure ens
                                 :index-of-last-enabling))

; The following must be true in order for the array access in enabled-numep to
; be in bounds.

       (< (access enabled-structure ens
                  :index-of-last-enabling)
          (access enabled-structure ens
                  :array-length))
       (character-listp (access enabled-structure ens
                                :array-name-root))
       (natp (access enabled-structure ens
                     :array-name-suffix))
       (equal (access enabled-structure ens
                      :array-length)
              (car (dimensions (access enabled-structure ens
                                       :array-name)
                               (access enabled-structure ens
                                       :theory-array))))))

; The following invariant is maintained in all instances of this structure.
; Theory-array is an array1p whose array length is array-length.  Furthermore
; array-name is a symbol of the form rootj, root is the array-name-root (as a
; list of characters) and j is the array-name-suffix (which however is not
; always used; see load-theory-into-enabled-structure).  Thus, if i is a
; nonnegative integer less than array-length, then (acl2-aref1 array-name
; theory-array i) has a satisfied guard.  Furthermore, important to efficiency
; but irrelevant to correctness, it will always be the case that the von
; Neumann array associated with array-name is in fact theory-array.  Thus the
; above expression executes quickly.  To get a new array name, should one ever
; be needed, it can suffice to increment the array-name-suffix and build a name
; from that new value.  However, if we hope to use parallel evaluation in the
; waterfall, we instead make a unique name based on each clause-id.  See
; load-theory-into-enabled-structure.

; The theory-array of an enabled-structure for a given common theory is (except
; for the header entry) just the augmented runic theory corresponding to the
; given common theory.  That is, the ACL2 array alist we need to construct for
; a theory maps each array index to a non-nil value.  The non-nil value we
; choose is in fact the corresponding rune.  It would suffice, for purposes of
; enabling, to store T in the array to signify enabledness.  By storing the
; rune itself we make it possible to determine what runic theory is in the
; array.  (There is no general purpose way to map from a nume to its rune
; (short of looking through the whole world).)

; The global variable 'global-enabled-structure contains an instance of the
; enabled-structure record in which the array-name is ENABLED-ARRAY-0,
; array-name-root is the list of characters in "ENABLED-ARRAY-" and the
; array-name-suffix is 0.  A rune with nume n is (globally) enabled in the
; current world iff either n is greater than the index-of-last-enabling or
; array[n] is non-nil.  This is just the computation done by enabled-numep,
; below.

; The in-theory event loads the 'global-enabled-structure with the theory-value
; and sets the index-of-last-enabling to the maximum nume at that time.  This
; structure is passed into prove and thus into rewrite, etc.

; When an in-theory hint setting is provided we change the array name
; appropriately and load the local theory into that structure.  We flush each
; such array in order to allow it to be garbage collected; see
; restore-hint-settings-in-pspv.

; Historical Note about Nqthm

; In nqthm we solved this problem by having a list of temporarily disabled
; names which was bound when there were local enabling hint settings.  That
; implementation suffered because if hundreds of names were enabled locally the
; time spent searching the list was excessive.  In xnqthm we solved that
; problem by storing the enabled status on the property list of each name.  We
; could do that here.  However, that implementation suffered from the fact that
; if a proof attempt was aborted then we had to carefully clean up the property
; list structures so that they once again reflected the current (global)
; theory.  The beauty of the ACL2 approach is that local hint settings have no
; affect on the global theory and yet involve no overhead.

; A delicacy of the current implementation however concerns the relation
; between the global enabled structure and undoing.  If the world is backed up
; to some previous point, the 'global-enabled-structure extant there is exposed
; and we are apparently ready to roll.  However, the von Neumann array named by
; that structure may be out-dated in the sense that it contains a now undone
; theory.  Technically there is nothing wrong with this, but if we let it
; persist things would be very slow because the attempt to access the
; applicative array would detect that the von Neumann array is out of date and
; would result in a linear search of the applicative array.  We must therefore
; compress the applicative array (and hence reload the von Neumann one)
; whenever we back up.

; Finally, there is one last problem.  Eventually the array-size of the array
; in one of these structures will be too small.  This manifests itself when the
; maximum rule index at the time we load the structure is equal to or greater
; than the array-length.  At that time we grow the array size by 500.

; Here is how we use an enabled structure, ens, to determine if a nume, rune,
; or function is enabled.

(defun enabled-numep (nume ens)

; This function takes a nume (or nil) and determines if it is enabled
; in the enabled structure ens.  We treat nil as though it were
; enabled.

  (declare (type (or null (integer 0 *))
                 nume)
           (xargs :guard (enabled-structure-p ens)))
  (cond ((null nume) t)
        ((> nume
            (the-fixnum
             (access enabled-structure ens :index-of-last-enabling)))
         t)
        (t (aref1 (access enabled-structure ens :array-name)
                  (access enabled-structure ens :theory-array)
                  (the-fixnum nume)))))

(defun enabled-arith-numep (nume ens)

; This function takes a nume (or nil) and determines if it is enabled in the
; enabled structure ens.  We treat nil as though it were enabled.  In current
; usage, ens is always the global arithmetic theory.  Any nume created since
; the most recent in-arithmetic-theory is considered disabled.  The normal
; enabled-numep would treat these more recent numes as enabled.

; Our calls of the-fixnum assume that nume is less than about 2 billion.  That
; seems like a safe assumption!

  (cond ((null nume) t)
        ((> (the-fixnum nume)
            (the-fixnum
             (access enabled-structure ens :index-of-last-enabling)))
         nil)
        (t (aref1 (access enabled-structure ens :array-name)
                  (access enabled-structure ens :theory-array)
                  (the-fixnum nume)))))

(defun enabled-runep (rune ens wrld)

; This takes a rune and determines if it is enabled in the enabled structure
; ens.  Since fnume returns nil on fake-runes, this function answers that a
; fake rune is enabled.  See also active-runep.

  (declare (xargs :guard
                  (and (plist-worldp wrld)
                       (consp rune)
                       (consp (cdr rune))
                       (symbolp (base-symbol rune))
                       (enabled-structure-p ens)
                       (nat-alistp (getpropc (base-symbol rune)
                                             'runic-mapping-pairs nil
                                             wrld)))
                  :guard-hints (("Goal" :do-not-induct t))))
  (enabled-numep (fnume rune wrld) ens))

(defmacro active-runep (rune)

; Warning: Keep this in sync with active-or-non-runep.

; This takes a rune and determines if it is enabled in the enabled structure
; ens.  Unlike enabled-runep, this returns nil if the rune is a fake-rune or is
; not a runep in the given wrld.  See also active-or-non-runep.

  `(let* ((rune ,rune)
          (nume (and (consp rune)
                     (consp (cdr rune))
                     (symbolp (cadr rune))

; The tests above guard the call of fnume just below, the same way that runep
; guards the computation made in its body from the property list.

                     (fnume rune (w state)))))
     (and nume
          (enabled-numep nume ens))))

(defmacro active-or-non-runep (rune)

; Warning: Keep this in sync with active-runep.

; This takes a rune and determines if it is enabled in the enabled structure
; ens.  This also returns t if the rune is a fake-rune or is not a runep in the
; given wrld.  See also active-runep.

  `(let* ((rune ,rune)
          (nume (and (consp rune)
                     (consp (cdr rune))
                     (symbolp (cadr rune))

; The tests above guard the call of fnume just below, the same way that runep
; guards the computation made in its body from the property list.

                     (fnume rune (w state)))))
     (or (not nume)
         (enabled-numep nume ens))))

(defun enabled-xfnp (fn ens wrld)

; Fn must be either a function symbol or lambda expression, i.e., something you
; might get from ffn-symb of a term.  If fn is a lambda expression or a
; constrained function symbol, we return t.  Otherwise, we consider
; (:EXECUTABLE-COUNTERPART fn), and answer whether it is enabled.

; Note: This function exploits the fact that nil is considered enabled by
; enabled-numep.

; Note: Suppose you want to determine whether (:DEFINITION fn) is enabled.
; Perhaps you really want to know if the latest definition rule for fn that has
; non-nil :install-body field is enabled; and you may also want to ask other
; questions about the def-body of fn.  Then this function is not the one
; to use!

  (cond ((flambdap fn) t)
        (t (enabled-numep (fn-rune-nume fn t t wrld) ens))))

(mutual-recursion

(defun sublis-var! (alist term ens wrld ttree)

; This function applies alist to term and evaluates any ground subexpressions
; in that result.  We return (mv term' flg ttree') where term' is the resulting
; term, ttree' is an extension of ttree containing the executable-counterparts
; used, and flg is t iff term' is a quoted constant.  We avoid running disabled
; functions.  The flg result is probably not interesting to callers outside of
; this nest.

; This function's behavior on lambda applications is a little strange.
; Consider

; 1. ((lambda (x) (+ (+ 1 1) x)) 1)         ==> 3
; 2. ((lambda (x) (+ (+ 1 1) (undef x))) 1) ==> (+ 2 (undef 1))
; 3. ((lambda (x) (+ (+ 1 1) x)) a)         ==> ((lambda (x) (+ (+ 1 1) x)) a)

; Note: these examples are merely suggestive; binary-+ is a primitive and
; cons-term evaluates it.

; If the actuals to a lambda application are all constants, we take a chance
; and open up the lambda.  See example 1.  This will generally produce a
; constant.  But of course, that path through the lambda body may lead to
; constrained or disabled functions and then we'll get an expanded lambda, as
; in 2.  But if the actuals to the lambda are not all constants, we don't even
; try, as in 3.  This means that constant subexpressions inside the lambda body
; are still present, even though partial evaluation might lead even to a
; constant.

  (cond
   ((variablep term)
    (let ((a (assoc-eq term alist)))
      (cond (a (mv (cdr a) (quotep (cdr a)) ttree))
            (t (mv term nil ttree)))))
   ((fquotep term)
    (mv term t ttree))
   ((flambda-applicationp term)
    (mv-let
     (args flg ttree)
     (sublis-var!-lst alist (fargs term) ens wrld ttree)
     (cond
      (flg ; (all-quoteps args)
       (sublis-var! (pairlis$ (lambda-formals (ffn-symb term)) args)
                    (lambda-body (ffn-symb term))
                    ens wrld ttree))
      (t (mv (cons-term (ffn-symb term) args)
             nil
             ttree)))))
   ((eq (ffn-symb term) 'if)
    (mv-let
     (arg1 flg1 ttree)
     (sublis-var! alist (fargn term 1) ens wrld ttree)
     (cond
      (flg1
       (if (cadr arg1)
           (sublis-var! alist (fargn term 2) ens wrld ttree)
           (sublis-var! alist (fargn term 3) ens wrld ttree)))
      (t (mv-let
          (arg2 flg2 ttree)
          (sublis-var! alist (fargn term 2) ens wrld ttree)
          (mv-let
           (arg3 flg3 ttree)
           (sublis-var! alist (fargn term 3) ens wrld ttree)
           (declare (ignore flg3))

; We optimize (if x y y) just because we can.  We could do a lot more
; if-optimization here if it turns out to be needed.

           (cond ((equal arg2 arg3)

; If arg2 and arg3 are the same, then they are both quotes or not, so flg2
; suffices for the resulting flag.

                  (mv arg2 flg2 ttree))
                 (t (mv (fcons-term* 'if arg1 arg2 arg3)
                        nil
                        ttree)))))))))
   (t (mv-let
       (args flg ttree)
       (sublis-var!-lst alist (fargs term) ens wrld ttree)
       (cond

; The following test was taken from rewrite with a few modifications
; for the formals used.

        ((and flg                             ; (all-quoteps args)
              (logicp (ffn-symb term) wrld) ; maybe fn is being admitted
              (enabled-xfnp (ffn-symb term) ens wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall-w below disallows the use of attachments (last
; parameter, aok, is nil).

              (not (getpropc (ffn-symb term) 'constrainedp nil wrld)))
         (mv-let
          (erp val)
          (pstk
           (ev-fncall-w (ffn-symb term) (strip-cadrs args) wrld
                        nil ; user-stobj-alist
                        nil t t nil))
          (cond
           (erp
            (mv (cons-term (ffn-symb term) args) nil ttree))
           (t (mv (kwote val)
                  t
                  (push-lemma (fn-rune-nume (ffn-symb term) nil t wrld)
                              ttree))))))
        (t (mv (cons-term (ffn-symb term) args) nil ttree)))))))

(defun sublis-var!-lst (alist lst ens wrld ttree)
  (cond ((null lst) (mv nil t ttree))
        (t (mv-let
            (x flg1 ttree)
            (sublis-var! alist (car lst) ens wrld ttree)
            (mv-let
             (y flg2 ttree)
             (sublis-var!-lst alist (cdr lst) ens wrld ttree)
             (mv (cons x y)
                 (and flg1 flg2)
                 ttree))))))
)

; Before we develop the code for loading a theory into an enabled
; structure, we put down code for warning when leaving a 0-ary
; function disabled while its executable-counterpart is enabled.

(defun theory-warning-fns-aux (runes1 runes2 max-nume
                                      nume prev-rune1 prev-rune2 w acc)

; See the comment in theory-warning-fns for a general discussion, in particular
; of (1), (2), and (3) below.  We apply reverse to the returned accumulator in
; order to return function symbols in the order in which they were defined (a
; minor aesthetic preference).

  (declare (type (signed-byte 30) nume))
  (cond
   ((eql nume max-nume)
    (reverse acc))
   (t
    (let* ((found1 (eql (caar runes1) nume))
           (found2 (eql (caar runes2) nume))
           (curr-rune1 (and found1 (cdar runes1)))
           (curr-rune2 (and found2 (cdar runes2)))
           (rest-runes1 (if found1 (cdr runes1) runes1))
           (rest-runes2 (if found2 (cdr runes2) runes2)))
      (theory-warning-fns-aux
       rest-runes1 rest-runes2 max-nume (1+f nume) curr-rune1 curr-rune2 w
       (if (and (eq (car curr-rune2) :executable-counterpart)
                (null prev-rune2)                        ; (1)
                (not (and curr-rune1 (null prev-rune1))) ; (2)
                (null (formals (cadr curr-rune2) w)))    ; (3)
           (cons (cadr curr-rune2) acc)
         acc))))))

(defun theory-warning-fns (ens1 ens2 w)

; Here is our strategy for producing warnings when an in-theory event or hint
; leaves us with a 0-ary function whose :executable-counterpart is enabled but
; :definition is not.  We assume that we have our hands on two enabled
; structures: the pre-existing one, which we call ens1, and the one created by
; the in-theory event or hint, which we call ens2 and is returned by
; load-theory-into-enabled-structure.  Note that the length of ens2 is at least
; as great as the length of ens1.  We walk through all indices (numes) of ens1.
; When do we find something worth warning about?  We only have a problem when
; we find an enabled :executable-counterpart at the current nume in ens2.  By
; the Essay on the Assignment of Runes and Numes by DEFUNS, we know that the
; previous nume represents the corresponding :definition.  Three conditions
; must now hold: (1) The preceding (:definition) rune is disabled in ens2; (2)
; The same problem was not already present in ens1; and (3) The function in
; question is 0-ary.

; We deal with the arrays as lists ordered by car, rather than using aref1,
; because the two arrays may have the same name in which case the first one is
; probably out of date.  We apply cdr to remove the headers.

  (theory-warning-fns-aux (cdr (access enabled-structure ens1 :theory-array))
                          (cdr (access enabled-structure ens2 :theory-array))
                          (1+ (access enabled-structure ens2
                                      :index-of-last-enabling))
                          0 nil nil w nil))

(defun@par maybe-warn-about-theory (ens1 force-xnume-en1 imm-xnume-en1 ens2
                                         ctx wrld state)

; Ens1 is the enabled structure before an in-theory event or hint, and ens2 is
; the resulting enabled structure.  It is a bit unfortunate that warning-off-p
; is checked twice, but that is a trivial inefficiency, certainly overshadowed
; by the savings in calling theory-warning-fns needlessly.

; Force-xnume-en1 is the enabled status of forcing (*force-xnume*) in ens1.
; Imm-xnume-en1 is the status immediate force mode
; (*immediate-force-modep-xnume*) in ens1.

  (cond
   ((warning-disabled-p "Disable")
    (state-mac@par))
   (t (pprogn@par
       (let ((fns (theory-warning-fns ens1 ens2 wrld)))
         (if fns
             (warning$@par ctx ("Disable")
               "The following 0-ary function~#0~[~/s~] will now have ~#0~[its ~
                :definition rune~/their :definition runes~] disabled but ~
                ~#0~[its :executable-counterpart rune~/their ~
                :executable-counterpart runes~] enabled, which will allow ~
                ~#0~[its definition~/their definitions~] to open up after ~
                all:  ~&0.~|See :DOC theories."
               fns)
           (state-mac@par)))
       (cond
        ((and force-xnume-en1
              (not (enabled-numep *force-xnume* ens2)))
         (warning$@par ctx ("Disable")
           "Forcing has transitioned from enabled to disabled.~|See :DOC ~
            force."))
        ((and (not force-xnume-en1)
              (enabled-numep *force-xnume* ens2))
         (warning$@par ctx ("Disable")
           "Forcing has transitioned from disabled to enabled.~|See :DOC ~
            force."))
        (t (state-mac@par)))
       (cond
        ((and imm-xnume-en1
              (not (enabled-numep *immediate-force-modep-xnume* ens2)))
         (warning$@par ctx ("Disable")
           "IMMEDIATE-FORCE-MODEP has transitioned from enabled to ~
            disabled.~|See :DOC force."))
        ((and (not imm-xnume-en1)
              (enabled-numep *immediate-force-modep-xnume* ens2))
         (warning$@par ctx ("Disable")
           "IMMEDIATE-FORCE-MODEP has transitioned from disabled to ~
            enabled.~|See :DOC immediate-force-modep."))
        (t (state-mac@par)))))))

; And now we develop the code for loading a theory into an enabled
; structure.

(defrec theory-invariant-record
  ((tterm . error) . (untrans-term . book))
  t)

(defun enabled-disabled-runeps (exprs enableds disableds)
  (cond ((endp exprs)
         (mv nil (reverse enableds) (reverse disableds)))
        (t (let ((e (car exprs)))
             (case-match e
               (('active-runep ('quote rune))
                (enabled-disabled-runeps (cdr exprs)
                                         (cons rune enableds)
                                         disableds))
               (('not ('active-runep ('quote rune)))
                (enabled-disabled-runeps (cdr exprs)
                                         enableds
                                         (cons rune disableds)))
               (& (mv t nil nil)))))))

(defun theory-invariant-msg-implication (runeps1 runeps2)
  (mv-let (flg enableds1 disableds1)
    (enabled-disabled-runeps (if (eq (car runeps1) 'and)
                                 (cdr runeps1)
                               (list runeps1))
                             nil nil)
    (and (null flg) ; no error
         (mv-let (flg enableds2 disableds2)
           (enabled-disabled-runeps (if (eq (car runeps2) 'and)
                                        (cdr runeps2)
                                      (list runeps2))
                                    nil nil)
           (and (null flg)                ; no error
                (or enableds1 disableds1) ; should always be true
                (or enableds2 disableds2) ; should always be true
                (let* ((en  "the rune~#0~[ ~&0 is~/s ~&0 are~] enabled")
                       (dis "the rune~#0~[ ~&0 is~/s ~&0 are~] not enabled")
                       (msg0 (and enableds1  (msg en  enableds1)))
                       (msg1 (and enableds1 disableds1 " and "))
                       (msg2 (and disableds1 (msg dis disableds1)))
                       (msg3 (and enableds2  (msg en  enableds2)))
                       (msg4 (and enableds2 disableds2 " and "))
                       (msg5 (and disableds2 (msg dis disableds2))))
                  (msg "~|which asserts that if ~@0~@1~@2, then ~@3~@4~@5"
                       (or msg0 "") (or msg1 "") (or msg2 "")
                       (or msg3 "") (or msg4 "") (or msg5 ""))))))))

(defun combine-ands (x y)
  (case-match x
    (('and . a)
     (case-match y
       (('and . b)
        `(and ,@a ,@b))
       (& `(and ,@a y))))
    (&
     (case-match y
       (('and . a)
        `(and ,x ,@a))
       (& `(and ,x ,y))))))

(defun theory-invariant-msg-active-runep-lst (lst acc)
  (cond ((atom lst)
         (and (cdr acc)
              (msg "~|which asserts that the runes ~&0 are not ~
                    ~#1~[both~/all~] enabled at the same time"
                   (reverse acc)
                   (cdr acc))))
        (t (let ((form (car lst)))
             (case-match form
               (('active-runep ('quote rune))
                (theory-invariant-msg-active-runep-lst (cdr lst)
                                                       (cons rune acc)))
               (t ""))))))

(defun theory-invariant-msg (form)
  (case-match form
    (('not ('and . active-runep-lst))
     (and (consp active-runep-lst)
          (consp (cdr active-runep-lst))
          (theory-invariant-msg-active-runep-lst active-runep-lst nil)))
    (('not ('active-runep ('quote rune)))
     (msg "~|which asserts that the rune ~x0 is not enabled"
          rune))
    (('incompatible rune1 rune2 . &)
     (msg "~|which asserts that the runes ~x0 and ~x1 are not both enabled at ~
           the same time"
          rune1 rune2))
    (('incompatible! rune1 rune2 . &)
     (msg "~|which asserts that the runes ~x0 and ~x1 are not both enabled at ~
           the same time"
          rune1 rune2))
    (('or ('not active-runeps1) active-runeps2)
     (theory-invariant-msg `(if ,active-runeps1
                                ,active-runeps2
                              t)))
    (('if active-runeps1
         ('if active-runeps2 concl 't)
       't)
     (theory-invariant-msg `(if ,(combine-ands active-runeps1
                                               active-runeps2)
                                ,concl
                              t)))
    (('if active-runeps1
         ('or ('not active-runeps2) concl)
       't)
     (theory-invariant-msg `(if ,(combine-ands active-runeps1
                                               active-runeps2)
                                ,concl
                              t)))
    (('if active-runeps1 active-runeps2 't)
     (theory-invariant-msg-implication active-runeps1 active-runeps2))
    (& nil)))

(defrec certify-book-info

; The useless-runes-info field is first here because that is the field that
; changes the most often, in the case that we are using data from the
; @useless-runes.lsp file.  It can have any of the following forms; a
; capitalized symbol indicates that exact symbol in the "ACL2" package.

; NIL
;   We are not doing anything with useless-runes.

; (CHANNEL chan . pkg-names)
;   Chan is an output channel for writing to the @useless-runes.lsp file.
;   Pkg-names lists the known package names in the certification world,
;   including those that are hidden.

; (FAST-ALIST . fal)
;   Fal is a fast-alist, each of whose pairs associates an event name (a
;   symbol) with a list of "useless" runes for that event.

; (THEORY . augmented-theory)
;   Augmented-theory is associated with the current event in the global
;   fast-alist.

  (useless-runes-info include-book-phase cert-op . full-book-name)
  nil) ; could replace with t sometime

(defun active-useless-runes (state)
  (let ((certify-book-info (f-get-global 'certify-book-info state)))
    (and certify-book-info
         (let ((useless-runes-info (and certify-book-info
                                        (access certify-book-info
                                                certify-book-info
                                                :useless-runes-info))))
           (and (eq (car useless-runes-info) 'THEORY)
                (cdr useless-runes-info))))))

(defun useless-runes-filename (full-book-name)

; This is analogous to expansion-filename, but for the file containing useless
; rune information.  See expansion-filename.

  (let ((len (length full-book-name))
        (posn (search *directory-separator-string* full-book-name
                      :from-end t)))
    (assert$ (and (equal (subseq full-book-name (- len 5) len) ".lisp")
                  posn)
             (concatenate 'string
                          (subseq full-book-name 0 posn)
                          "/.sys"
                          (subseq full-book-name posn (- len 5))
                          "@useless-runes.lsp"))))

(defun active-useless-runes-filename (state)

; This is analogous to expansion-filename, but for the file containing useless
; rune information.  See expansion-filename.  NOTE: This function does not
; check that the resulting file actually exists!

  (let* ((info (f-get-global 'certify-book-info state)))
    (and info
         (useless-runes-filename
          (access certify-book-info info :full-book-name)))))

(defun@par chk-theory-invariant1 (theory-expr ens invariant-alist errp-acc ctx
                                              state)

; We check a theory represented in enabled structure ens against the theory
; invariants in invariant-alist.  If theory-expr is :from-hint then this theory
; comes from an :in-theory hint, and if it is :install then it is from
; installing a world; otherwise, theory-expr is a theory expression
; corresponding to this theory.

  (cond
   ((null invariant-alist)
    (mv@par errp-acc nil state))
   (t (let* ((table-entry (car invariant-alist))
             (inv-name (car table-entry))
             (inv-rec (cdr table-entry))
             (theory-inv (access theory-invariant-record inv-rec :tterm)))
        (mv-let
          (erp okp latches)
          (ev theory-inv
              (list (cons 'ens ens)
                    (cons 'state (coerce-state-to-object state)))
              state
              nil
              nil t)
          (declare (ignore latches))
          (cond
           (erp (let* ((produced-by-msg
                        (cond ((eq theory-expr :from-hint)
                               "an :in-theory hint")
                              ((eq theory-expr :install)
                               "the current event")
                              (t (msg "~x0" theory-expr))))
                       (theory-invariant-term
                        (access theory-invariant-record inv-rec
                                :untrans-term))
                       (msg (msg
                             "Theory invariant ~x0 could not be evaluated on ~
                              the theory produced by ~@1~@2.  Theory invariant ~
                              ~P43 produced the error message:~%~@5~@6  See ~
                              :DOC theory-invariant."
                             inv-name
                             produced-by-msg
                             (if (active-useless-runes state)
                                 (msg ", modified by subtracting the theory ~
                                       for the current event stored in file ~
                                       ~s0"
                                      (active-useless-runes-filename state))
                               "")
                             (term-evisc-tuple nil state)
                             theory-invariant-term
                             okp ; error message
                             (if (access theory-invariant-record inv-rec :error)
                                 "~|This theory invariant violation causes an ~
                                  error."
                               ""))))
                  (mv-let@par
                   (errp-acc state)
                   (cond
                    ((access theory-invariant-record inv-rec :error)
                     (mv-let@par (erp val state)
                                 (er@par soft ctx "~@0" msg)
                                 (declare (ignore erp val))
                                 (mv@par t state)))
                    (t (pprogn@par (warning$@par ctx "Theory"
                                     `("~@0"
                                       (:error-msg ,okp)
                                       (:produced-by-msg ,produced-by-msg)
                                       (:theory-invariant-name ,inv-name)
                                       (:theory-invariant-term
                                        ,theory-invariant-term))
                                     msg)
                                   (mv@par errp-acc state))))
                   (chk-theory-invariant1@par theory-expr ens
                                              (cdr invariant-alist)
                                              errp-acc ctx state))))
           (okp (chk-theory-invariant1@par theory-expr ens (cdr invariant-alist)
                                           errp-acc ctx state))
           (t (let* ((produced-by-msg
                      (cond ((eq theory-expr :from-hint)
                             "an :in-theory hint")
                            ((eq theory-expr :install)
                             "the current event")
                            (t (msg "~x0" theory-expr))))
                     (theory-invariant-term
                      (access theory-invariant-record inv-rec
                              :untrans-term))
                     (theory-invariant-book
                      (access theory-invariant-record inv-rec
                              :book))
                     (thy-inv-msg
                      (theory-invariant-msg theory-invariant-term))
                     (msg (msg
                           "Theory invariant ~x0, defined ~@1, failed on the ~
                            theory produced by ~@2~@3.  Theory invariant ~x0 is ~
                            ~@4~@5  See :DOC theory-invariant."
                           inv-name
                           (if (null theory-invariant-book)
                               "at the top-level"
                             (msg "in book ~x0" theory-invariant-book))
                           produced-by-msg
                           (if (active-useless-runes state)
                               (msg ", modified by subtracting the theory for ~
                                     the current event stored in file ~s0"
                                    (active-useless-runes-filename state))
                             "")
                           (if thy-inv-msg
                               (msg "~P10~@2."
                                    (term-evisc-tuple nil state)
                                    theory-invariant-term
                                    thy-inv-msg)
                             (msg "~P10."
                                    (term-evisc-tuple nil state)
                                    theory-invariant-term))
                           (if (access theory-invariant-record inv-rec :error)
                               "~|This theory invariant violation causes an ~
                               error."
                             ""))))
                (mv-let@par
                 (errp-acc state)
                 (cond
                  ((access theory-invariant-record inv-rec :error)
                   (mv-let@par (erp val state)
                               (er@par soft ctx "~@0" msg)
                               (declare (ignore erp val))
                               (mv@par t state)))
                  (t (pprogn@par (warning$@par ctx "Theory"
                                   `("~@0"
                                     (:produced-by-msg ,produced-by-msg)
                                     (:theory-invariant-name ,inv-name)
                                     (:theory-invariant-term
                                      ,theory-invariant-term))
                                   msg)
                                 (mv@par errp-acc state))))
                 (chk-theory-invariant1@par theory-expr ens
                                            (cdr invariant-alist)
                                            errp-acc ctx state))))))))))

(defun@par chk-theory-invariant (theory-expr ens ctx state)

; See the comment in chk-theory-invariant1.

  (chk-theory-invariant1@par theory-expr
                             ens
                             (table-alist 'theory-invariant-table (w state))
                             nil
                             ctx
                             state))

; CLAUSE IDENTIFICATION

; Before we can write the function that prints a description of
; simplify-clause's output, we must be able to identify clauses.  This raises
; some issues that are more understandable later, namely, the notion of the
; pool.  See Section PUSH-CLAUSE and The Pool.

; Associated with every clause in the waterfall is a unique object
; called the clause identifier or clause-id.  These are printed out
; at the user in a certain form, e.g.,

; [3]Subgoal *2.1/5.7.9.11'''

; but the internal form of these ids is as follows.

(defrec clause-id

; Warning: Keep this in sync with clause-id-p.

; Forcing-round is a natural number, pool-lst and case-lst are generally
; true-lists of non-zero naturals (though elements of case-lst can be of the
; form Dk in the case of a dijunctive split) and primes is a natural.  The
; pool-lst is indeed a pool-lst.  (See the function pool-lst.) The case-lst is
; structurally analogous.

  ((forcing-round . pool-lst) case-lst . primes)
  t)

(defun pos-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (posp (car l))
                (pos-listp (cdr l))))))

(defun all-digits-p (lst radix)
  (declare (xargs :guard (and (character-listp lst)
                              (integerp radix)
                              (<= 2 radix)
                              (<= radix 36))))
  (cond ((endp lst) t)
        (t (and (digit-char-p (car lst) radix)
                (all-digits-p (cdr lst) radix)))))

(defun d-pos-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (null lst))
        ((natp (car lst))
         (d-pos-listp (cdr lst)))
        (t (and (symbolp (car lst))
                (let ((name (symbol-name (car lst))))
                  (and (not (equal name ""))
                       (eql (char name 0) #\D)
                       (all-digits-p (cdr (coerce name 'list)) 10)))
                (d-pos-listp (cdr lst))))))

(defun clause-id-p (cl-id)

; Warning: Keep this in sync with (defrec clause-id ...).

  (declare (xargs :guard t))
  (case-match cl-id
    (((forcing-round . pool-lst) case-lst . primes)
     (and (natp forcing-round)
          (pos-listp pool-lst)
          (d-pos-listp case-lst)
          (natp primes)))
    (& nil)))

; A useful constant, the first clause-id:

(defconst *initial-clause-id*

; Note: If this changes, inspect every use of it.  As of this writing there is
; one place where we avoid a make clause-id and use *initial-clause-id* instead
; because we know the forcing-round is 0 and pool-lst and case-lst fields are
; both nil and the primes field is 0.

  (make clause-id
        :forcing-round 0
        :pool-lst nil
        :case-lst nil
        :primes 0))

; Because of the way :DO-NOT-INDUCT name hints are implemented, and because of
; the way we create names of theory arrays, we need to be able to produce a
; string representing a given clause-id.  In the case of the above
; :DO-NOT-INDUCT, we use this to form a literal atom of the form |name
; clause-id| where clause-id is what tilde-@-clause-id-phrase will print on id.
; Therefore, we now virtually repeat the definition of
; tilde-@-clause-id-phrase, except this time building a string.  We could use
; this to print all clause ids.  But that is slow because it involves consing
; up strings.  So we suffer the inconvenience of duplication.  If
; tilde-@-clause-id-phrase is changed, be sure to change the functions below.

(defun chars-for-tilde-@-clause-id-phrase/periods (lst)
  (declare (xargs :guard (d-pos-listp lst)))
  (cond
   ((null lst) nil)
   ((null (cdr lst)) (explode-atom (car lst) 10))
   (t (append (explode-atom (car lst) 10)
              (cons #\.
                    (chars-for-tilde-@-clause-id-phrase/periods
                     (cdr lst)))))))

(defun chars-for-tilde-@-clause-id-phrase/primes (n)
  (declare (xargs :guard (and (integerp n) (>= n 0))))
  (cond ((= n 0) nil)
        ((= n 1) '(#\'))
        ((= n 2) '(#\' #\'))
        ((= n 3) '(#\' #\' #\'))
        (t (cons #\' (append (explode-atom n 10) '(#\'))))))

(defun chars-for-tilde-@-clause-id-phrase (id)
  (declare (xargs :guard (clause-id-p id)))
  (append
   (if (= (access clause-id id :forcing-round) 0)
       nil
     `(#\[ ,@(explode-atom (access clause-id id :forcing-round) 10) #\]))
   (cond ((null (access clause-id id :pool-lst))
          (cond ((null (access clause-id id :case-lst))
                 (append '(#\G #\o #\a #\l)
                         (chars-for-tilde-@-clause-id-phrase/primes
                          (access clause-id id :primes))))
                (t (append '(#\S #\u #\b #\g #\o #\a #\l #\Space)
                           (chars-for-tilde-@-clause-id-phrase/periods
                            (access clause-id id :case-lst))
                           (chars-for-tilde-@-clause-id-phrase/primes
                            (access clause-id id :primes))))))
         (t (append
             '(#\S #\u #\b #\g #\o #\a #\l #\Space #\*)
             (chars-for-tilde-@-clause-id-phrase/periods
              (access clause-id id :pool-lst))
             (cons #\/
                   (append (chars-for-tilde-@-clause-id-phrase/periods
                            (access clause-id id :case-lst))
                           (chars-for-tilde-@-clause-id-phrase/primes
                            (access clause-id id :primes)))))))))

(defun string-for-tilde-@-clause-id-phrase (id)

; Warning: Keep this in sync with tilde-@-clause-id-phrase.

  (declare (xargs :guard (clause-id-p id)))
  (coerce (chars-for-tilde-@-clause-id-phrase id)
          'string))

(defun update-enabled-structure-array (name header alist k old d new-n)

; This function makes a number of assumptions, including the assumption noted
; below that if k is non-nil, then the first k keys of alist form a strictly
; decreasing sequence.

; We have considered trying to optimize this function.  We found that only 961
; out of the approximately 871,000 calls during (include-book "centaur/sv/top"
; :dir :system) were with k = nil, and these accounted only for less than 5% of
; the time spent in this function.  We also found that when k is not nil, the
; average value of k during evaluation of that same include-book is 11.1, which
; seems pretty small.  So perhaps there isn't much opportunity for further
; optimization here.

  #+acl2-loop-only
  (declare (xargs :guard (and (array1p name (cons header alist))
                              (null (array-order header))
                              (or (eq k nil)
                                  (and (natp k)
                                       (<= k (length alist))))
                              (natp d)
                              (<= new-n d)))
           (ignore k old d new-n))
  #+acl2-loop-only
  (compress1 name (cons header alist))
  #-acl2-loop-only
  (declare (ignore name))
  #-acl2-loop-only
  (let ((old-car (car old))
        (ar0 (cadr old))
        (k2 (or k (length alist))) ; number of array elements to set
        index)
    (assert (= 1 (array-rank ar0)))
    (assert (eq (car (car old-car)) :HEADER))
    (assert (or (eq k nil)
                (eq (nthcdr k alist)
                    (cdr old-car))))
    (assert (eq header (car old-car)))
    (assert (<= new-n d)) ; necessity is explained in a comment below
    (setf (car old) *invisible-array-mark*)

; If we are to build the array from scratch (which is the case k = nil),
; then set all entries of the array to nil.

    (when (eq k nil)
      (loop for i from 0 to (1- d)
            do
            (setf (svref ar0 i) nil)))

; Next set relevant entries in the array according to enabled status.

    (loop for i from 1 to k2
          for tail on alist
          do
          (let ((new-index (caar tail)))

; We check that the keys are decreasing, as a way of ensuring that there are no
; duplicates.

            (assert (or (null index)
                        (< new-index index)))
            (setq index new-index)
            (setf (svref ar0 index) (cdar tail))))

; Finally, return the new theory-array, which is placed into the car of old.

    (setf (car old) (cons header alist))))

(defun increment-array-name (ens incrmt-array-name-info)
  (let* ((root (access enabled-structure ens :array-name-root))
         (suffix (cond ((eq incrmt-array-name-info t)
                        (1+ (access enabled-structure ens
                                    :array-name-suffix)))
                       (t (access enabled-structure ens
                                  :array-name-suffix))))
         (name (cond ((eq incrmt-array-name-info t)
                      (intern (coerce
                               (append root
                                       (explode-nonnegative-integer suffix
                                                                    10
                                                                    nil))
                               'string)
                              "ACL2"))
                     ((keywordp incrmt-array-name-info)
                      incrmt-array-name-info)
                     (incrmt-array-name-info ; must be a clause-id
                      (intern (coerce
                               (append root
                                       (chars-for-tilde-@-clause-id-phrase
                                        incrmt-array-name-info))
                               'string)
                              "ACL2"))
                     (t (access enabled-structure ens :array-name)))))
    (mv root suffix name)))

(defun update-enabled-structure (ens n d new-d alist augmented-p
                                     incrmt-array-name-info)
  #+acl2-loop-only (declare (ignore d augmented-p))
  #-acl2-loop-only
  (when (and (null incrmt-array-name-info)
             augmented-p
             (int= d new-d))
    (let* ((k 0)
           (name (access enabled-structure ens :array-name))
           (old (get-acl2-array-property name))
           (header (cadddr old))
           (old-n (access enabled-structure ens :index-of-last-enabling)))
      (when (and header ; hence old is associated with name
                 (consp (car old))
                 (eq header (caar old))
                 (or (eq (loop for tail on alist
                               do (cond ((<= (caar tail) old-n)
                                         (return tail))
                                        (t (incf k))))
                         (cdr (access enabled-structure ens :theory-array)))

; The disjunct just above computes the tail of alist consisting of entries
; not exceeding the old index-of-last-enabling, and checks that this tail is
; the alist stored in the existing enabled structure.  In that case, k is the
; number of entries of alist outside that tail, and the call of
; update-enabled-structure-array below can take advantage of the fact that only
; the first k elements of alist need to be updated in the corresponding raw
; Lisp array.

; By including the following disjunct and also tweaking
; load-theory-into-enabled-structure, we have reduced the time spent in
; load-theory-into-enabled-structure from about 3.1 to 3.2s to about 2.7s to
; 2.8s in runs (of (include-book "centaur/sv/top" :dir :system)) that take
; about 58s.  Notice that by setting k = nil, we are indicating to the call
; below of update-enabled-structure-array that the eq test above has failed.

                     (and (<= old-n n)
                          (progn (setq k nil) t))))
        (assert (eq (access enabled-structure ens :theory-array)
                    (car old))) ; checking this invariant before updating
        (return-from
         update-enabled-structure
         (change enabled-structure ens
                 :index-of-last-enabling n
                 :theory-array (update-enabled-structure-array
                                name header alist k old d n))))))
  (mv-let (root suffix name)
    (increment-array-name ens incrmt-array-name-info)
    (make enabled-structure
          :index-of-last-enabling n
          :theory-array
          (compress1 name
                     (cons (list :header
                                 :dimensions (list new-d)
                                 :maximum-length (1+ new-d)
                                 :default nil
                                 :name name
                                 :order nil)
                           alist))
          :array-name name
          :array-length new-d
          :array-name-root root
          :array-name-suffix suffix)))

(defun load-theory-into-enabled-structure-1 (theory augmented-p ens
                                                    incrmt-array-name-info
                                                    index-of-last-enabling
                                                    wrld)

; See load-theory-into-enabled-structure, which is a wrapper for this function
; that may perform an extra check.

  (let* ((n (or index-of-last-enabling (1- (get-next-nume wrld))))
         (d (access enabled-structure ens :array-length))
         (new-d (cond ((< n d) d)
                      (t (max (* 2 d)
                              (+ d (* 500 (1+ (floor (- n d) 500))))))))
         (alist (if augmented-p
                    theory
                  (augment-runic-theory theory wrld))))
    (update-enabled-structure ens n d new-d alist
                              augmented-p
                              incrmt-array-name-info)))

(defun@par load-theory-into-enabled-structure
  (theory-expr theory augmented-p ens incrmt-array-name-info
               index-of-last-enabling wrld ctx state)

; Note: Theory must be a runic theory if augmented-p is nil and otherwise an
; augmented runic theory, but never a common theory.

; We do exactly what the name of this function says, we load the given theory
; into the enabled structure ens.  If incrmt-array-name-info is t we increment
; the array name suffix.  If incrmt-array-name-info is non-boolean, then it is
; either a keyword (see comment in load-hint-settings-into-rcnst), or else a
; clause-id that we use to create a new name uniquely determined by that
; clause-id.  Otherwise, incrmt-array-name-info is nil and we use the same
; name.  Loading consists of augmenting the theory (if augmented-p is nil) to
; convert it into a list of pairs, (nume . rune), mapping numes to their runes,
; and then compressing it into the named array.  We set the index of last
; enabling to be the highest existing nume in wrld right now unless
; index-of-last-enabling is non-nil, in which case we use that (which should be
; a natp).  Thus, any name introduced after this is enabled relative to this
; ens.  If the array of the ens is too short, we extend it.

; A Refresher Course on ACL2 One Dimensional Arrays:

; Suppose that a is an array with :dimension (d) and :maximum-length
; m.  Then you access it via (aref1 'name a i).  It must be the case
; that i<d.  If every slot of a were filled, the length of a would be
; d, but the maximum index would be d-1, since indexing is 0-based.
; You set elements with (aset1 'name a i val).  That increases the
; length of a by 1.  When (length a) > m, a compress is done.  If an
; array is never modified, then the minimum acceptable m is in fact d+1.

; Note:  Every call of this function should be followed by a call of
; maybe-warn-about-theory on the enabled structure passed in and the one
; returned.

  (let ((ens (load-theory-into-enabled-structure-1
              theory augmented-p ens incrmt-array-name-info
              index-of-last-enabling wrld)))
    (er-progn@par (if (or (eq theory-expr :no-check)
                          (eq (ld-skip-proofsp state)
                              'include-book)
                          (eq (ld-skip-proofsp state)
                              'include-book-with-locals))
                      (value@par nil)
                    (chk-theory-invariant@par theory-expr ens ctx state))
                  (value@par ens))))

; Here is how we initialize the global enabled structure, from which
; all subsequent structures are built.

(defun initial-global-enabled-structure (root-string)

; We generate an initial enabled-structure in which everything is enabled.
; The array is empty but of length d (which is the constant 1000 here).
; The array name is formed by adding a "0" to the end of root-string.
; The array-name-root is the list of characters in root-string and the suffix
; is 0.

  (let* ((root (coerce root-string 'list))
         (name (intern (coerce (append root '(#\0)) 'string)
                       "ACL2"))
         (d 1000))
    (make enabled-structure
          :index-of-last-enabling -1
          :theory-array (compress1 name
                                   (cons (list :header
                                               :dimensions (list d)
                                               :maximum-length (1+ d)
                                               :default nil
                                               :name name)
                                         nil))
          :array-name name
          :array-length d
          :array-name-root root
          :array-name-suffix 0)))

; And here is the function that must be used when you undo back to a
; previous value of the global enabled structure:

(defun recompress-global-enabled-structure (varname wrld)

; Logically speaking this function is a no-op that returns t.  It is
; only called from #-acl2-loop-only code.  Practically speaking it
; side-effects the von Neumann array named in the global-enabled-
; structure so that it once again contains the current array.

; This function is called when you have reason to believe that the von
; Neumann array associated with the global enabled structure is out of
; date.  Suppose that wrld, above, was obtained from the then current
; ACL2 world by rolling back, as with UBT.  Then there is possibly a
; new 'global-enabled-structure in wrld.  But the array associated
; with it is still the one from the now-no-longer current ACL2 world.
; We just compress the new array again.  Because the array was already
; compressed, we know compress1 returns an eq object and so we don't
; actually have to store its value back into the global-enabled-structure.
; Indeed, we don't want to do that because it would require us to put a
; new binding of 'global-enabled-structure on wrld and we don't want to
; to do that.  (Once upon a time we did, and it was inconvenient because
; it covered up the most recent command-landmark; indeed, sometimes there
; would be two successive bindings of it.)

; Parallelism wart: it's unclear whether we need to lock this array operation.
; By design, each array and theory is unique to the current subgoal, so this
; locking should be unnecessary.  However, we've seen some slow array access
; warnings, and maybe this is where they're generated.

; (with-acl2-lock
;  *acl2-par-arrays-lock*

  (let ((ges1 (getpropc varname 'global-value nil wrld)))
    (cond (ges1 (prog2$ (maybe-flush-and-compress1
                         (access enabled-structure ges1 :array-name)
                         (access enabled-structure ges1 :theory-array))
                        t))
          (t t))))

(defun recompress-stobj-accessor-arrays (stobj-names wrld)

; This function has nothing to do with theories, but we place it here because
; it has a similar function to recompress-global-enabled-structure, defined
; just above.  This function should be called when the 'accessor-names arrays
; (used for printing nth/update-nth accesses to stobjs) might be out of date.

  (if (endp stobj-names)
      t
    (let* ((st (car stobj-names))
           (ar (getpropc st 'accessor-names nil wrld)))
      (prog2$ (or (null ar)
                  (maybe-flush-and-compress1 st ar))
              (recompress-stobj-accessor-arrays (cdr stobj-names) wrld)))))

; We have defined all the basic concepts having to do with theories
; except the interface to the user, i.e., the "theory manipulation
; functions" with which the user constructs theories, the polite and
; verbose theory checkers that ensure that a theory expression
; produced a theory, and the events for defining theories and setting
; the current one.  We do these things later and return now to the
; development of type-set.

; The Type-set-xxx Functions

; We are about to embark on a litany of definitions for determining
; the type-set of various function applications, given the type-sets
; of certain of their arguments.  There is no fixed style of
; definition here; because type-set is so often called, we thought it
; best to pass in only those arguments actually needed, rather than
; adhere to some standard style.  All of the functions return a type
; set and a ttree.  The ttree is always used as an accumulator in the
; sense that we may extend but may not ignore the incoming ttree.

; This raises a problem: Suppose that the ttree records our work in
; establishing the type set, ts, of an argument but that we ultimately
; ignore ts because it is not strong enough to help.  If we return the
; extended ttree, we might cause unnecessary case splits (justifying
; the irrelevant fact that the arg has type-set ts).  We adopt the
; convention of passing in two ttrees, named ttree and ttree0.  Ttree
; is always an extension of ttree0 and records the work done to get
; the argument type sets.  Therefore, we may return ttree (possibly
; extended) if our answer is based on the argument type sets, and may
; return ttree0 otherwise (which merely passes along unknown
; previously done work of any sort, not necessarily only work done on this
; particular term -- so do not return nil instead of ttree0!).

; The primitive type-set functions all push the following fake rune into the
; ttree they return, so that we know that primitive type-set knowledge was
; used.  Before we invented this fake rune, we attributed this type-set
; reasoning to propositional calculus, i.e., we would report that (implies
; (integerp x) (integerp (1- x))) was proved by trivial observations.  But we
; prefer to think of it (and report it) as type reasoning.  See the Essay on
; Fake-Runes for a discussion of fake runes.

(defconst *fake-rune-for-type-set*
  '(:FAKE-RUNE-FOR-TYPE-SET nil))

; To make it convenient to push this rune into a tree we provide:

(defun puffert (ttree)

; Once upon a time this function was called Push-Fake-Rune-for-Type-Set.  It
; got shortened to pfrts and pronounced "pufferts".  The name stuck except that
; the final s was dropped to make it more like a first-person verb form.  You
; know, ``I puffert'', ``you puffert'', ``he pufferts.''  Here, we frequently
; puffert ttrees.  Right.

  (push-lemma *fake-rune-for-type-set* ttree))

(defun immediate-forcep (fn ens)

; This function must return 'case-split, t or nil!

  (cond ((eq fn 'case-split) 'case-split)
        ((enabled-numep *immediate-force-modep-xnume* ens) t)
        (t nil)))

(defmacro numeric-type-set (ts)

; Warning:  This is a dangerous macro because it evaluates ts more than once!
; It is best if the argument is a variable symbol.

; This coerces ts into the type *ts-acl2-number*.  That is, if ts contains
; nonnumeric bits then those bits are shut off and *ts-zero* is turned on.
; Another way to look at it is that if term has type ts then (fix term) has
; type (numeric-type-set ts).

; Note:  We tried wrapping (the-type-set ...) around the form below, inside the
; backquote, but found that (disassemble 'TYPE-SET-BINARY-+) produced identical
; results either way.

  `(let ((numeric-ts-use-nowhere-else
          (ts-intersection (check-vars-not-free
                            (numeric-ts-use-nowhere-else)
                            ,ts)
                           *ts-acl2-number*)))
     (if (ts= numeric-ts-use-nowhere-else ,ts)
         ,ts
       (ts-union numeric-ts-use-nowhere-else *ts-zero*))))

(defmacro rational-type-set (ts)

; Warning:  This is a dangerous macro because it evaluates ts more than once!
; It is best if the argument is a variable symbol.

; This macro is like numeric-type-set, but coerces ts to the rationals.  Note
; that it reuses the special variable numeric-ts-use-nowhere-else even though
; this is a slight misnomer.

  `(let ((numeric-ts-use-nowhere-else
          (ts-intersection (check-vars-not-free
                            (numeric-ts-use-nowhere-else)
                            ,ts)
                           *ts-rational*)))
     (if (ts= numeric-ts-use-nowhere-else ,ts)
         ,ts
       (ts-union numeric-ts-use-nowhere-else *ts-zero*))))

;; Historical Comment from Ruben Gamboa:
;; I added this function analogously to rational-type-set.

#+:non-standard-analysis
(defmacro real-type-set (ts)

; Warning:  This is a dangerous macro because it evaluates ts more than once!
; It is best if the argument is a variable symbol.

; This macro is like numeric-type-set, but coerces ts to the reals.  Note
; that it reuses the special variable numeric-ts-use-nowhere-else even though
; this is a slight misnomer.

  `(let ((numeric-ts-use-nowhere-else
          (ts-intersection (check-vars-not-free
                            (numeric-ts-use-nowhere-else)
                            ,ts)
                           *ts-real*)))
     (if (ts= numeric-ts-use-nowhere-else ,ts)
         ,ts
       (ts-union numeric-ts-use-nowhere-else *ts-zero*))))

; We start with probably the most complicated primitive type set
; function, that for binary-+.

(defun type-set-binary-+ (term ts1 ts2 ttree ttree0)

; Because 1- (i.e., SUB1) is so common and often is applied to
; strictly positive integers, it is useful to know that, in such
; cases, the result is a non-negative integer.  We therefore test for
; (+ x -1) and its commuted version (+ -1 x).  To be predictable, we
; also look for (+ x +1), and its commuted version, when x is strictly
; negative.  We specially arrange for the answer type-set to be empty
; if either of the input type-sets is empty.  This occurs when we are
; guessing type sets.  The idea is that some other branch ought to
; give us a nonempty type-set before this one can meaningfully
; contribute to the answer.  Before we added the special processing of
; +1 and -1 we did not have to check for the empty case because the
; array referenced by aref2 has the property that if either type-set
; is empty the result is empty.

  (let ((arg1 (fargn term 1))
        (arg2 (fargn term 2)))
    (cond ((or (ts= ts1 *ts-empty*)
               (ts= ts2 *ts-empty*))
           (mv *ts-empty* ttree))
          ((and (equal arg2 ''-1)
                (ts-subsetp ts1 *ts-positive-integer*))
           (mv *ts-non-negative-integer* (puffert ttree)))
          ((and (equal arg1 ''-1)
                (ts-subsetp ts2 *ts-positive-integer*))
           (mv *ts-non-negative-integer* (puffert ttree)))
          (t (let ((ans (aref2 'type-set-binary-+-table
                               *type-set-binary-+-table*
                               (numeric-type-set ts1)
                               (numeric-type-set ts2))))
               (mv ans
                   (puffert (if (ts= ans *ts-acl2-number*)
                                ttree0
                              ttree))))))))

(defun type-set-binary-* (ts1 ts2 ttree ttree0)

; See type-set-binary-+ for a few comments.

  (cond ((or (ts= ts1 *ts-empty*)
             (ts= ts2 *ts-empty*))
         (mv *ts-empty* ttree))
        (t (let ((ans (aref2 'type-set-binary-*-table
                             *type-set-binary-*-table*
                             (numeric-type-set ts1)
                             (numeric-type-set ts2))))
             (mv ans
                 (puffert (if (ts= ans *ts-acl2-number*)
                              ttree0
                            ttree)))))))

(defun type-set-not (ts ttree ttree0)
  (cond
   ((ts= ts *ts-nil*)
    (mv *ts-t* (puffert ttree)))
   ((ts-subsetp *ts-nil* ts)
    (mv *ts-boolean* ttree0))
   (t (mv *ts-nil* (puffert ttree)))))

(defun type-set-<-1 (r arg2 commutedp type-alist)

; We are trying to determine the truth value of an inequality, (< arg1
; arg2) where arg1 is (quote r), a rational constant.  Except, in the
; case that commutedp is non-nil the inequality at issue is (< arg2
; (quote r)).

; We scan through the type-alist looking for inequalities that imply
; the truth or falsity of the inequality at issue, and return two
; values --- the determined type of the inequality, by default
; *ts-boolean*, and a governing ttree.

; Here is a trivial example of the problem this code is intended to
; solve.

;  (defstub bar (x) t)
;
;  (defaxiom bar-thm
;    (implies (and (integerp x)
;                  (< 3 x))
;             (bar x))
;    :rule-classes :type-prescription)
;
;  (thm
;   (implies (and (integerp x)
;                 (< 4 x))
;            (bar x)))

; Robert Krug came up with the original version of this patch when
; playing with arithmetic functions that changed sign at some point
; other than zero.  Conceptually, this type of reasoning belongs to
; linear arithmetic rather than type-set, but it provides a modest
; improvement at a very small cost.  In a perfect world we might want
; to mix type-set reasoning with the linear arithmetic; the ability to
; call add-poly from within type-set or assume-true-false could be
; nice (although perhaps too expensive).

  (cond ((endp type-alist)
         (mv *ts-boolean* nil))
        (t
         (let ((type-alist-entry (car type-alist)))
           (case-match type-alist-entry
             ((typed-term type . ttree)
              (mv-let (c leftp x)

; We bind c to nil if we cannot use type-alist-entry.  Otherwise, c is a
; rational that is being compared with < to a term x, and leftp is true if and
; only if c occurs on the left side of the <.  We postpone the check that x is
; equal to arg2, which is potentially expensive, until we need to make that
; check (if at all).

                      (case-match typed-term
                        (('< ('quote c) x)
                         (if (rationalp c)
                             (mv c t x)
                           (mv nil nil x)))
                        (('< x ('quote c))
                         (if (rationalp c)
                             (mv c nil x)
                           (mv nil nil nil)))
                        (& (mv nil nil nil)))
                      (cond
                       ((null c)
                        (type-set-<-1 r arg2 commutedp (cdr type-alist)))
                       (leftp

; So type refers to (c < x).

                        (cond
                         ((and (<= r c)
                               (ts= type *ts-t*)
                               (equal x arg2))

;   (r <= c < arg2) implies (r < arg2), and hence also not (arg2 < r).

                          (mv (if commutedp *ts-nil* *ts-t*)
                              (puffert ttree)))
                         ((and (if commutedp (< c r) (<= c r))
                               (ts= type *ts-nil*)
                               (equal x arg2))

;   (arg2 <= c <= r) implies not (r < arg2);
;   (arg2 <= c <  r) implies (arg2 < r).

                          (mv (if commutedp *ts-t* *ts-nil*)
                              (puffert ttree)))
                         (t
                          (type-set-<-1 r arg2 commutedp (cdr type-alist)))))
                       (t ; (not leftp)

; So type refers to (arg2 < c).

                        (cond
                         ((and (if commutedp (<= r c) (< r c))
                               (ts= type *ts-nil*)
                               (equal x arg2))

;   (r <  c <= arg2) implies (r < arg2);
;   (r <= c <= arg2) implies not (arg2 < r).

                          (mv (if commutedp *ts-nil* *ts-t*)
                              (puffert ttree)))
                         ((and (<= c r)
                               (ts= type *ts-t*)
                               (equal x arg2))

;   (arg2 < c <= r) implies not (r < arg2) and also implies (arg2 < r).

                          (mv (if commutedp *ts-t* *ts-nil*)
                              (puffert ttree)))
                         (t
                          (type-set-<-1 r arg2 commutedp
                                        (cdr type-alist))))))))
             (& (type-set-<-1 r arg2 commutedp (cdr type-alist))))))))

;; Historical Comment from Ruben Gamboa:
;; I changed complex-rational to complex below.

(defun type-set-< (arg1 arg2 ts1 ts2 type-alist ttree ttree0 pot-lst pt)

; This function is not cut from the standard mold because instead of
; taking term it takes the two args.  This allows us easily to
; implement certain transformations on inequalities: When x is an
; integer,

; (<  x 1) is (not (< 0 x)) and
; (< -1 x) is (not (< x 0)).

; Warning: It is important to assume-true-false that type-set-< make
; these transformations.  See the comments about type-set-< in
; assume-true-false.

; As of Version_2.6, this function diverged even further from the standard
; mold.  We now use the type-alist to determine the truth or falsity
; of some simple inequalities which would be missed otherwise.
; See type-set-<-1 for details.

  (let* ((nts1 (numeric-type-set ts1))
         (nts2 (numeric-type-set ts2)))
    (cond ((and (equal arg2 *1*)

; Actually we don't have to add 0 back in, as done by numeric-type-set, before
; making the following test.  But let's keep things simple.

                (ts-subsetp nts1 *ts-integer*))
           (mv-let (ts ttree)
                   (type-set-< *0* arg1 *ts-zero* ts1
                               type-alist
                               (puffert ttree)

; Note: Once upon a time in v2-7, ttree0 was used immediately below
; instead of ttree.  Note however that we have depended upon ts1 to
; get here.  It might be unsound to do that and then report the
; dependencies of ttree0.  However, in v2-7 this was (probably) sound
; because the ttree0 exits were all reporting *ts-boolean* answers.
; But in the new code, below, we use add-polys0 in a way that could
; overwrite ttree with ttree0.  Put more intuitively: we think v2-7
; was sound even with a ttree0 here, but we think v2-8 would be
; unsound with a ttree0 here because of the add-polys0 below.

                               ttree
                               pot-lst pt)
                   (type-set-not ts ttree ttree0)))
          ((and (equal arg1 *-1*)
                (ts-subsetp nts2 *ts-integer*))
           (mv-let (ts ttree)
                   (type-set-< arg2 *0* ts2 *ts-zero*
                               type-alist
                               (puffert ttree)
; See note above about this ttree versus the old ttree0.
                               ttree
                               pot-lst pt)
                   (type-set-not ts ttree ttree0)))

; If one of the args is a constant (a quotep) we look in the
; type-alist.  If we get a useful answer, we are done.  Note that if
; we do get a useful answer here, it is sufficient to use ttree0
; rather than ttree since our answer does not depend on the type of
; the args.  In particular, type-set-<-1 returns an accurate answer
; regardless of whether we make the tests above leading to here.  See
; the comments following ``The Type-set-xxx Functions'' above for an
; explanation of ttree0 vs. ttree.

          (t
           (mv-let (returned-ts returned-ttree)
             (cond
              ((and (quotep arg1) (rationalp (cadr arg1)))
               (type-set-<-1 (cadr arg1) arg2 nil type-alist))
              ((and (quotep arg2) (rationalp (cadr arg2)))
               (type-set-<-1 (cadr arg2) arg1   t type-alist))
              (t
               (mv *ts-boolean* nil)))
             (if (not (ts= returned-ts *ts-boolean*))
                 (mv returned-ts
                     (cons-tag-trees returned-ttree
                                     ttree0))

; We did not get a useful answer by looking in the type-alist.  We try
; 'type-set-<-table if we can.

               (let ((temp-ts
                      (if (or (ts-intersectp ts1
                                             #+:non-standard-analysis
                                             *ts-complex*
                                             #-:non-standard-analysis
                                             *ts-complex-rational*)
                              (ts-intersectp ts2
                                             #+:non-standard-analysis
                                             *ts-complex*
                                             #-:non-standard-analysis
                                             *ts-complex-rational*))
                          *ts-boolean*
                        (aref2 'type-set-<-table
                               *type-set-<-table* nts1 nts2))))
                 (cond ((or (ts= temp-ts *ts-t*)
                            (ts= temp-ts *ts-nil*))
                        (mv temp-ts (puffert ttree)))
                       ((null pot-lst)
                        (mv *ts-boolean* ttree0))

; We finally try using linear arithmetic by calling add-polys on, first,
; the negation of the original inequality.  If this returns a contradictionp,
; the original inequality must be true.  If this does not return a
; contradictionp, we try linear arithmetic with the original inequality.
; These final two tries are new to v2-8.

                       (t

; Note: Below there are two calls of base-poly, each of which has the
; ttree ttree0.  The argument that we're not dependent on ts1 and ts2
; here is as follows.  The setting of temp-ts, above, which appears to
; rely on ts1 and ts2, is irrelevant here because if we get here,
; temp-ts is *ts-boolean*, which is correct regardless of the ttrees.
; Reader further above, the only uses of ts1 and ts2 are heuristic:
; the methods by which we compute an answer is correct even if the
; preceding tests were not made.

                        (mv-let (contradictionp new-pot-lst)
                          (add-polys0
                           (list (normalize-poly
                                  (add-linear-terms
                                   :lhs arg2
                                   :rhs arg1
                                   (base-poly ttree0
                                              '<=
; The following nil is the rational-poly-p flag and we could supply a
; more accurate value by looking at ts1 and ts2.  But then it would
; appear that we were depending on them.  Actually, we're not: the
; rational-poly-p flag is irrelevant to add-polys0 and could only come
; into play if the poly here created eventually found its way into a
; non-linear setting.  But that won't happen because the poly is
; thrown away.  However, since the flag is indeed irrelevant we just
; supply nil to avoid the appearance of dependence.

                                              nil
                                              nil))))
                           pot-lst pt nil 2)
                          (declare (ignore new-pot-lst))
                          (if contradictionp
                              (mv *ts-t* (access poly contradictionp :ttree))
                            (mv-let (contradictionp new-pot-lst)
                              (add-polys0
                               (list (normalize-poly
                                      (add-linear-terms
                                       :lhs arg1
                                       :rhs arg2
                                       (base-poly ttree0
                                                  '<
                                                  nil
                                                  nil))))
                               pot-lst pt nil 2)
                              (declare (ignore new-pot-lst))
                              (if contradictionp
                                  (mv *ts-nil*
                                      (access poly contradictionp :ttree))
                                (mv *ts-boolean* ttree0))))))))))))))

;; Historical Comment from Ruben Gamboa:
;; I added entries for real and complex irrationals.

(defun type-set-unary-- (ts ttree ttree0)
  (let ((ts1 (numeric-type-set ts)))
    (cond
     ((ts= ts1 *ts-acl2-number*)
      (mv *ts-acl2-number* ttree0))
     (t
      (mv (ts-builder ts1
                      (*ts-zero* *ts-zero*)
                      (*ts-one* *ts-negative-integer*)
                      (*ts-integer>1* *ts-negative-integer*)
                      (*ts-positive-ratio* *ts-negative-ratio*)
                      #+:non-standard-analysis
                      (*ts-positive-non-ratio* *ts-negative-non-ratio*)
                      (*ts-negative-integer* *ts-positive-integer*)
                      (*ts-negative-ratio* *ts-positive-ratio*)
                      #+:non-standard-analysis
                      (*ts-negative-non-ratio* *ts-positive-non-ratio*)
                      (*ts-complex-rational* *ts-complex-rational*)
                      #+:non-standard-analysis
                      (*ts-complex-non-rational* *ts-complex-non-rational*))
          (puffert ttree))))))

;; Historical Comment from Ruben Gamboa:
;; I added entries for real and complex irrationals.

(defun type-set-unary-/ (ts ttree ttree0)
  (let* ((ts1 (numeric-type-set ts))
         (ans (ts-builder ts1
                          (*ts-zero* *ts-zero*)
                          (*ts-one* *ts-one*)
                          (*ts-integer>1*
                           (ts-intersection0 *ts-positive-ratio*
                                             (ts-complement0 *ts-zero*)
                                             (ts-complement0 *ts-one*)))
                          (*ts-positive-ratio* *ts-positive-rational*)
                          (*ts-negative-rational* *ts-negative-rational*)
                          #+:non-standard-analysis
                          (*ts-positive-non-ratio* *ts-positive-non-ratio*)
                          #+:non-standard-analysis
                          (*ts-negative-non-ratio* *ts-negative-non-ratio*)
                          (*ts-complex-rational* *ts-complex-rational*)
                          #+:non-standard-analysis
                          (*ts-complex-non-rational*
                           *ts-complex-non-rational*))))
    (cond
     ((ts= ans *ts-acl2-number*)
      (mv *ts-acl2-number* (puffert ttree0)))
     (t
      (mv ans (puffert ttree))))))

(defun type-set-numerator (ts ttree ttree0)
  (let* ((ts1 (rational-type-set ts))
         (ans (ts-builder ts1
                          (*ts-zero* *ts-zero*)
                          (*ts-one* *ts-one*)
                          (*ts-integer>1* *ts-integer>1*)
                          (*ts-positive-ratio* *ts-positive-integer*)
                          (*ts-negative-rational* *ts-negative-integer*))))
    (cond ((ts= ans *ts-integer*)
           (mv *ts-integer* (puffert ttree0)))
          (t (mv ans (puffert ttree))))))

(defun type-set-denominator (ts ttree ttree0)
  (let* ((ts1 (rational-type-set ts))
         (ans (ts-builder ts1
                          (*ts-integer* *ts-one*)
                          (*ts-ratio* *ts-integer>1*))))
    (cond ((ts= ans *ts-positive-integer*)
           (mv *ts-positive-integer* (puffert ttree0)))
          (t (mv ans (puffert ttree))))))

;; Historical Comment from Ruben Gamboa:
;; I added an entry for *ts-complex-non-rational*.  Note that
;; since we don't know whether the type in non-rational because of an
;; irrational real or imaginary part, all we can say is that the
;; result is real, not necessarily irrational.

(defun type-set-realpart (ts ttree ttree0)
  (cond #+:non-standard-analysis
        ((ts-intersectp ts *ts-complex-non-rational*)
         (mv *ts-real* (puffert ttree0)))
        ((ts-intersectp ts *ts-complex-rational*)
         (mv *ts-rational* (puffert ttree0)))
        (t
         (mv (numeric-type-set ts) (puffert ttree)))))

;; Historical Comment from Ruben Gamboa:
;; I added an entry for *ts-complex-non-rational*.

(defun type-set-imagpart (ts ttree ttree0)
  (cond ((ts-subsetp ts *ts-complex-rational*)
         (mv (ts-union *ts-positive-rational*
                       *ts-negative-rational*)
             (puffert ttree)))
        #+:non-standard-analysis
        ((ts-subsetp ts *ts-complex*)
         (mv (ts-union *ts-positive-real*
                       *ts-negative-real*)
             (puffert ttree)))
        #+:non-standard-analysis
        ((ts-intersectp ts *ts-complex-non-rational*)
         (mv *ts-real* (puffert ttree0)))
        ((ts-intersectp ts *ts-complex-rational*)
         (mv *ts-rational* (puffert #+:non-standard-analysis ttree
                                    #-:non-standard-analysis ttree0)))
        (t
         (mv *ts-zero* (puffert ttree)))))

;; Historical Comment from Ruben Gamboa:
;; I allowed reals as well as rationals below for the type of
;; ts1 and ts2.

(defun type-set-complex (ts1 ts2 ttree ttree0)
  (let ((ts1 #+:non-standard-analysis
             (real-type-set ts1)
             #-:non-standard-analysis
             (rational-type-set ts1))
        (ts2 #+:non-standard-analysis
             (real-type-set ts2)
             #-:non-standard-analysis
             (rational-type-set ts2)))
    (cond ((ts= ts2 *ts-zero*)
           (mv ts1 (puffert ttree)))
          ((ts= (ts-intersection ts2 *ts-zero*)
                *ts-empty*)
           #+:non-standard-analysis
           (cond ((and (ts-subsetp ts1 *ts-rational*)
                       (ts-subsetp ts2 *ts-rational*))
                  (mv *ts-complex-rational* (puffert ttree)))
                 ((or (ts-subsetp ts1 *ts-non-ratio*)
                      (ts-subsetp ts2 *ts-non-ratio*))
                  (mv *ts-complex-non-rational* (puffert ttree)))
                 (t (mv *ts-complex* (puffert ttree))))
           #-:non-standard-analysis
           (mv *ts-complex-rational* (puffert ttree)))
          #+:non-standard-analysis
          ((ts= ts1 *ts-real*)
           (mv *ts-acl2-number* (puffert ttree0)))
          #-:non-standard-analysis
          ((ts= ts1 *ts-rational*)
           (mv *ts-acl2-number* (puffert ttree0)))
          (t
           (mv (ts-union ts1
                         #+:non-standard-analysis
                         (cond ((and (ts-subsetp ts1 *ts-rational*)
                                     (ts-subsetp ts2 *ts-rational*))
                                *ts-complex-rational*)
                               ((or (ts-subsetp ts1 *ts-non-ratio*)
                                    (ts-subsetp ts2 (ts-union *ts-non-ratio*
                                                              *ts-zero*)))
                                *ts-complex-non-rational*)
                               (t *ts-complex*))
                         #-:non-standard-analysis
                         *ts-complex-rational*)
               (puffert ttree))))))

;; Historical Comment from Ruben Gamboa:
;; I added this function to account for the new built-in floor1.

#+:non-standard-analysis
(defun type-set-floor1 (ts ttree ttree0)
  (let* ((ts1 (real-type-set ts))
         (ans (ts-builder ts1
                          (*ts-zero* *ts-zero*)
                          (*ts-one* *ts-one*)
                          (*ts-integer>1* *ts-integer>1*)
                          (*ts-positive-ratio* *ts-non-negative-integer*)
                          (*ts-positive-non-ratio* *ts-non-negative-integer*)
                          (*ts-negative-real* *ts-negative-integer*))))
    (cond ((ts= ans *ts-integer*)
           (mv *ts-integer* (puffert ttree0)))
          (t (mv ans (puffert ttree))))))

;; Historical Comment from Ruben Gamboa:
;; I added this function to account for the new built-in standard-part.

#+:non-standard-analysis
(defun type-set-standard-part (ts ttree ttree0)
  (let* ((ts1 (numeric-type-set ts))
         (ans (ts-builder ts1
                          (*ts-zero* *ts-zero*)
                          (*ts-one* *ts-one*)
                          (*ts-integer>1* *ts-integer>1*)
                          (*ts-positive-ratio* *ts-non-negative-real*)
                          (*ts-positive-non-ratio* *ts-non-negative-real*)
                          (*ts-negative-integer* *ts-negative-integer*)
                          (*ts-negative-ratio* *ts-non-positive-real*)
                          (*ts-negative-non-ratio* *ts-non-positive-real*)
                          (*ts-complex* *ts-acl2-number*))))
    (mv (ts-union (ts-intersection ts (ts-complement *ts-acl2-number*))
                  ans)
        (puffert (if (ts= ans *ts-acl2-number*)
                     ttree0
                     ttree)))))

;; Historical Comment from Ruben Gamboa:
;; I added this function to account for the new built-in standardp.

#+:non-standard-analysis
(defun type-set-standardp (ts ttree ttree0)
  (cond ((ts= ts *ts-zero*)
         (mv *ts-t* (puffert ttree)))
        ((ts= ts *ts-one*)
         (mv *ts-t* (puffert ttree)))
        (t (mv *ts-boolean* (puffert ttree0)))))

; Essay on Recognizer-Tuples

; The "recognizer-alist" of ACL2 is a virtual alist -- that is, a
; representation of a finite function -- rather than a single data structure.
; It associates a function symbol with a list of recognizer-tuple records that
; is stored on its 'recognizer-alist property.  This "alist" a combination of
; Nqthm's RECOGNIZER-ALIST and its two COMPOUND-RECOGNIZER-ALISTs.  (Historical
; note: Through Version_8.2 we stored a single alist rather than distributing
; the recognizer-alist across relevant function symbols.  But we made the
; change to support non-trivial efficiency improvements for large proof
; developments.)

(defrec recognizer-tuple

; Warning: In type-set-rec, we assume that the car of a recognizer-tuple cannot
; be the keyword :SKIP-LOOKUP.  Do not change the shape of this record to
; violate that assumption!  Visit all occurrences of :SKIP-LOOKUP if any such
; change is contemplated.

  (fn (nume . true-ts)
      (false-ts . strongp)
      . rune)
  t)

; The initial value of the recognizer-alist is shown after we discuss the
; meaning of these records.

; In a recognizer-tuple, fn is the name of some Boolean-valued
; function of one argument.  True-ts and and false-ts are type sets.
; If such a record is on the recognizer-alist then it is the case that
; (fn x) implies that the type set of x is a subset of true-ts and
; (not (fn x)) implies that the type set of x is a subset of false-ts.
; Furthermore, if strongp is t, then true-ts is the complement of
; false-ts; i.e., (fn x) recognizes exactly the subset identified by
; true-ts.  Rune is either a rune or
; *fake-rune-for-anonymous-enabled-rule*.  Nume is the nume of rune
; (possibly nil).

; For example, if we prove that

; (BOOLEANP X) -> (OR (EQUAL X T) (EQUAL X NIL))

; then we can add the following tuple

; (make recognizer-tuple
;       :fn BOOLEANP
;       :true-ts *ts-boolean*
;       :false-ts *ts-unknown*
;       :strongp nil
;       :nume nil
;       :rune *fake-rune-for-anonymous-enabled-rule*)

; to the list.  Observe that the false-ts for this pair does not tell us
; much.  But if we proved the above AND

; (NOT (BOOLEANP X)) -> (NOT (OR (EQUAL X T) (EQUAL X NIL)))

; we could add the tuple:

; (make recognizer-tuple
;       :fn BOOLEANP
;       :true-ts *ts-boolean*
;       :false-ts (ts-complement *ts-boolean*)
;       :strongp t)

; And we would know as much about BOOLEANP as we know about integerp.

; Consider the function PRIMEP.  It implies its argument is a positive integer
; greater than 1.  Its negation tells us nothing about the type of its
; argument.

; (make recognizer-tuple
;       :fn PRIMEP
;       :true-ts *ts-integer>1*
;       :false-ts *ts-unknown*
;       :strongp nil)

; Suppose now x is a term whose type set we know.  What is the type set of
; (PRIMEP x)?  If the type set for x includes the integer>1 bit, the type set
; for (PRIMEP x) may include *ts-t* so we will throw that in.  If the type set
; for x includes any of *ts-unknown*'s bits (of course it does) we will throw
; in *ts-nil*.  The interesting thing about this is that if the type set of x
; does not include the integers>1 bit, we'll know (PRIME x) is nil.

; If we assume (PRIME x) true, we will restrict the type of x to the integers >
; 1.  If we assume (PRIME x) false, we won't restrict x at all.

; Consider the function RATTREEP that recognizes cons-trees of
; rational numbers.  We can prove that (RATTREEP x) implies the type
; set of x is in *ts-cons* union *ts-rational*.  We can prove that
; (NOT (RATTREEP x)) implies that the type set of x is not
; *ts-rational*.  That means the false-ts for RATTREEP is the
; complement of the rationals.  If we were asked to get the type set
; of (RATTREEP x) where x is rational, we'd throw in a *ts-t* because
; the type of x intersects the true-ts and we'd not throw in anything
; else (because the type of x does not intersect the false ts).  If
; we were asked to assume (RATTREEP x) then on the true branch x's
; type would be intersected with the conses and the rationals.  On
; the false branch, the rationals would be deleted.

; Historical Note: In an earlier version of this code we did not allow
; compound recognizer rules to be enabled or disabled and hence did
; not store the runes and numes.  We were much cleverer then
; about allowing newly proved rules to strengthen existing recognizer
; tuples.  That is, you could prove a rule about the true-ts and then
; a second about the false-ts, and then perhaps a third tightening up
; the true-ts fact a little, etc.  This had the problem that it was
; not possible to identify a single rule name with the known facts
; about the type of fn.  Thus, when we decided to track use of all
; rules it was impossible to give a sensible meaning to disabled
; compound recognizer rules in some cases.  (E.g., the fact stored
; might be derived from both enabled and disabled rules.)  So an
; important aspect of the new design is that there is a 1:1
; correspondence between what we know and the rule that told us.  If
; you have proved a sequence of three rules about fn we will use the
; most recently proved, still-enabled one.  If you disable that one,
; we'll naturally fall back on the next most recently still-enabled
; one.

;; Historical Comment from Ruben Gamboa:
;; I added recognizers for realp and complexp.

(defconst *initial-recognizer-alist*
  (list (make recognizer-tuple
              :fn 'integerp
              :true-ts *ts-integer*
              :false-ts (ts-complement *ts-integer*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'rationalp
              :true-ts *ts-rational*
              :false-ts (ts-complement *ts-rational*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)

        #+:non-standard-analysis
        (make recognizer-tuple
              :fn 'realp
              :true-ts *ts-real*
              :false-ts (ts-complement *ts-real*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)

        (make recognizer-tuple
              :fn 'complex-rationalp
              :true-ts *ts-complex-rational*
              :false-ts (ts-complement *ts-complex-rational*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)

        #+:non-standard-analysis
        (make recognizer-tuple
              :fn 'complexp
              :true-ts *ts-complex*
              :false-ts (ts-complement *ts-complex*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)

        (make recognizer-tuple
              :fn 'acl2-numberp
              :true-ts *ts-acl2-number*
              :false-ts (ts-complement *ts-acl2-number*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'consp
              :true-ts *ts-cons*
              :false-ts (ts-complement *ts-cons*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'atom
              :true-ts (ts-complement *ts-cons*)
              :false-ts *ts-cons*
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'listp
              :true-ts (ts-union *ts-cons* *ts-nil*)
              :false-ts (ts-complement (ts-union *ts-cons* *ts-nil*))
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'true-listp
              :true-ts *ts-true-list*
              :false-ts (ts-complement *ts-true-list*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'characterp
              :true-ts *ts-character*
              :false-ts (ts-complement *ts-character*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'stringp
              :true-ts *ts-string*
              :false-ts (ts-complement *ts-string*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'null
              :true-ts *ts-nil*
              :false-ts (ts-complement *ts-nil*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)
        (make recognizer-tuple
              :fn 'symbolp
              :true-ts *ts-symbol*
              :false-ts (ts-complement *ts-symbol*)
              :strongp t
              :nume nil
              :rune *fake-rune-for-anonymous-enabled-rule*)))

(defun most-recent-enabled-recog-tuple1 (lst ens)

; This function finds the first recognizer-tuple in lst whose whose :nume is
; enabled-numep.  Thus, primitive recognizer tuples, like that for rationalp,
; are always "enabled."

  (cond ((endp lst) nil)
        ((enabled-numep (access recognizer-tuple (car lst) :nume) ens)
         (car lst))
        (t (most-recent-enabled-recog-tuple1 (cdr lst) ens))))

(defun most-recent-enabled-recog-tuple (fn wrld ens)

; This function finds the first recognizer-tuple for fn whose whose :nume is
; enabled-numep.  Thus, primitive recognizer tuples, like that for rationalp,
; are always "enabled."

  (let ((lst (getpropc fn 'recognizer-alist nil wrld)))
    (and lst ; optimization
         (most-recent-enabled-recog-tuple1 lst ens))))

(defun type-set-recognizer (recog-tuple arg-ts ttree ttree0)

; Recog-tuple is a recognizer-tuple.  Then we know that (fn x) implies
; that the type set of x, arg-ts, is a subset of true-ts.
; Furthermore, we know that ~(fn x) implies that arg-ts is a subset of
; false-ts.  In addition, we know that fn is a Boolean valued fn.

; This function is supposed to determine the type set of (fn x) where
; arg-ts is the type set of x.  Observe that if arg-ts intersects with
; true-ts then (fn x) might be true, so we should throw in *ts-t*.
; Conversely, if arg-ts does not intersect with true-ts then (fn x)
; cannot possibly be true.  Exactly analogous statements can be made
; about false-ts.

; We return two results, the type set of (fn x) and an extension of
; ttree (or ttree0) obtained by adding the named rule, tagged 'lemma.  We
; initially considered adding the rule name to the tree only if the
; type-set returned was stronger than just Boolean.  But it could be
; that this rule is the rule that established that fn was Boolean and
; so we can't be sure that even that weak response isn't an
; interesting use of this rule.

  (let ((ts (ts-builder
             arg-ts
             ((access recognizer-tuple recog-tuple :true-ts) *ts-t*)
             ((access recognizer-tuple recog-tuple :false-ts) *ts-nil*))))
    (cond
     ((ts= ts *ts-boolean*)
      (mv *ts-boolean*
          (push-lemma (access recognizer-tuple recog-tuple :rune) ttree0)))
     (t (mv ts
            (push-lemma (access recognizer-tuple recog-tuple :rune) ttree))))))

(defun type-set-car (ts ttree ttree0)
  (cond ((ts-intersectp ts *ts-cons*) (mv *ts-unknown* ttree0))
        (t (mv *ts-nil* ttree))))

(defun type-set-cdr (ts ttree ttree0)
  (let ((cdr-ts
         (ts-builder ts
                     (*ts-proper-cons* *ts-true-list*)
                     (*ts-improper-cons* (ts-complement *ts-true-list*))
                     (otherwise *ts-nil*))))
    (mv cdr-ts
        (if (ts= cdr-ts *ts-unknown*)
            ttree0
          (puffert ttree)))))

(defun type-set-coerce (term ts1 ts2 ttree1 ttree2 ttree0)

  (cond ((equal (fargn term 2) ''list)

; If the first argument is of type *ts-string* then the result could
; be either nil or a proper cons.  But if the first argument isn't
; possibly a string, the result is NIL.

         (cond ((ts-intersectp *ts-string* ts1)

; We are not really using ts1 here because (coerce x 'list) is always
; a true list.  So we report ttree0, not ttree1.

                (mv *ts-true-list* (puffert ttree0)))
               (t (mv *ts-nil* (puffert ttree1)))))
        ((quotep (fargn term 2))
         (mv *ts-string* (puffert ttree0)))
        ((ts-disjointp *ts-non-t-non-nil-symbol* ts2)
; Observe that the first argument (and its ttree1) don't matter here.
         (mv *ts-string* (puffert ttree2)))
        (t (mv (ts-union *ts-true-list* *ts-string*) (puffert ttree0)))))

(defun type-set-intern-in-package-of-symbol (ts1 ts2 ttree1 ttree2 ttree0)
  (cond ((ts-disjointp ts1 *ts-string*)
         (mv *ts-nil* (puffert ttree1)))
        ((ts-disjointp ts2 *ts-symbol*)
         (mv *ts-nil* (puffert ttree2)))
        (t (mv *ts-symbol* (puffert ttree0)))))

(defun type-set-length (ts ttree ttree0)
  (let ((ans (ts-builder ts
                         (*ts-string* *ts-non-negative-integer*)
                         (*ts-cons* *ts-positive-integer*)
                         (otherwise *ts-zero*))))
    (cond
     ((ts= ans *ts-integer*)
      (mv *ts-integer* (puffert ttree0)))
     (t
      (mv ans (puffert ttree))))))

(defun type-set-cons (ts2 ttree ttree0)

; Ts2 is the type set of the second argument of the cons.

  (let ((ts (ts-builder ts2
                        (*ts-true-list* *ts-proper-cons*)
                        (otherwise *ts-improper-cons*))))
    (cond ((ts= ts *ts-cons*)
           (mv ts (puffert ttree0)))
          (t (mv ts (puffert ttree))))))

(defconst *singleton-type-sets*

; Keep this constant in sync with the Essay on Strong Handling of *ts-one* and
; code discussed in that Essay.

  (list *ts-t* *ts-nil* *ts-zero* *ts-one*))

(defun type-set-equal (ts1 ts2 ttree ttree0)
  (cond ((member ts1 *singleton-type-sets*)
         (cond ((ts= ts1 ts2) (mv *ts-t* (puffert ttree)))
               ((ts-intersectp ts1 ts2)
                (mv *ts-boolean* (puffert ttree0)))
               (t (mv *ts-nil* (puffert ttree)))))
        ((ts-intersectp ts1 ts2)
         (mv *ts-boolean* (puffert ttree0)))
        (t (mv *ts-nil* (puffert ttree)))))

;; Historical Comment from Ruben Gamboa:
;; I added entries here for realp evg.  This is probably not
;; needed, since we can't construct realp numbers!

(defun type-set-quote (evg)

; Most type-set-xxx functions return a pair consisting of a ts and a ttree.
; But the ttree is irrelevant here and so we don't waste the time passing
; it around.  We return the ts of the evg.

  (cond ((atom evg)
         (cond ((rationalp evg)
                (cond ((integerp evg)
                       (cond ((int= evg 0) *ts-zero*)
                             ((int= evg 1) *ts-one*)
                             ((> evg 0) ; equivalently, (> evg 1)
                              *ts-integer>1*)
                             (t *ts-negative-integer*)))
                      ((> evg 0) *ts-positive-ratio*)
                      (t *ts-negative-ratio*)))

               #+:non-standard-analysis
               ((realp evg)
                (cond ((> evg 0) *ts-positive-non-ratio*)
                      (t *ts-negative-non-ratio*)))

               ((complex-rationalp evg)
                *ts-complex-rational*)

               #+:non-standard-analysis
               ((complexp evg)
                *ts-complex-non-rational*)

               ((symbolp evg)
                (cond ((eq evg t) *ts-t*)
                      ((eq evg nil) *ts-nil*)
                      (t *ts-non-t-non-nil-symbol*)))
               ((stringp evg) *ts-string*)
               (t *ts-character*)))
        ((true-listp evg)
         *ts-proper-cons*)
        (t *ts-improper-cons*)))

(defun type-set-char-code (ts ttree ttree0)

; (char-code x) is always a non-negative integer.  If x is not a
; characterp, then its code is 0.  If x is a character, its code
; might be 0 or positive.

  (cond ((ts-disjointp ts *ts-character*)
         (mv *ts-zero* (puffert ttree)))
        (t (mv *ts-non-negative-integer* (puffert ttree0)))))

(defun fn-count-1 (flg x fn-count-acc p-fn-count-acc)

; Warning: Keep this in sync with the var-fn-count-1.

; This definition is similar to var-fn-count-1, except that it counts only fns
; and pseudo-fns, not vars.  It was introduced when a check of fn-counts was
; added to ancestors-check1, in order to improve efficiency a bit.  (We now use
; var-fn-count for that purpose.)  A 2.6% decrease in user time (using Allegro
; 5.0.1) was observed when the fn-counts check was added, yet that test was
; found to be critical in certain cases (see the comment in ancestors-check1).

; We discovered that the Allegro compiler does not do as good a job at tail
; recursion elimination for mutual recursion nests as for single recursion.  So
; we code this as a singly recursive function with a flag, flg:  When flg is
; nil then x is a term, and otherwise x is a list of terms.  We have since also
; taken advantage of the use of this single "flag" function when verifying
; termination and guards.

  (declare (xargs :guard (and (if flg
                                  (pseudo-term-listp x)
                                (pseudo-termp x))
                              (integerp fn-count-acc)
                              (integerp p-fn-count-acc))
                  :verify-guards NIL))
  (cond (flg
         (cond ((atom x)
                (mv fn-count-acc p-fn-count-acc))
               (t
                (mv-let (fn-cnt p-fn-cnt)
                        (fn-count-1 nil (car x) fn-count-acc p-fn-count-acc)
                        (fn-count-1   t (cdr x) fn-cnt p-fn-cnt)))))
        ((variablep x)
         (mv fn-count-acc p-fn-count-acc))
        ((fquotep x)
         (mv fn-count-acc
             (+ p-fn-count-acc (fn-count-evg (cadr x)))))
        (t (fn-count-1 t (fargs x) (1+ fn-count-acc) p-fn-count-acc))))

(defmacro fn-count (term)
  `(fn-count-1 nil ,term 0 0))

(defun term-order (term1 term2)

; See term-order1 for comments.

  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (term-order1 term1 term2 nil))

; Type Prescriptions

; A type-prescription is a structure, below, that describes how to
; compute the type of a term.  They are stored on the property list of
; the top function symbol of the term, under the property
; 'type-prescriptions.  Unlike Nqthm's "type-prescription-lst" ANY
; enabled type-prescription in 'type-prescriptions may contribute to
; the type-set of the associated function symbol.

(defrec type-prescription

; Warning: If you change this, consider changing conjoin-type-prescriptions.

  (basic-ts (nume . term)
            (hyps . backchain-limit-lst)
            (vars . rune)
            . corollary)
  t)

; Term is a term, hyps is a list of terms, basic-ts is a type-set, and vars is
; a list of variables that occur in term.  Let term' be some instance of term
; under the substitution sigma.  Then, provided the sigma instance of hyps is
; true, the type-set of term' is the union of basic-ts with the type-sets of
; the sigma images of the vars.  Corollary is the theorem (translated term)
; from which this type-prescription was derived.  For system-generated
; type-prescriptions it is a term created by convert-type-prescription-to-term.
; Backchain-limit-lst must either be nil, or else a list containing only nil
; and natural numbers, of the same length as hyps.

; (Note: Why do we store the corollary when we could apparently recompute it
; with convert-type-prescription-to-term?  The reason is that the computation
; is sensitive to the ens in use and we do not wish the corollary for a
; type-prescription rule to change as the user changes the global enabled
; structure.)

; For example, for APP we might have the type-prescription:

; (make type-prescription :rune ... :nume ...
;       :term (app x y)
;       :hyps ((true-listp x))
;       :basic-ts *ts-cons*
;       :vars '(y)
;       :corollary (implies (true-listp x)
;                           (if (consp (app x y))
;                               't
;                               (equal (app x y) y))))

; The above example corresponds to what we'd get from the lemma:
; (implies (true-listp x)
;          (or (consp (app x y))
;              (equal (app x y) y)))

; When type-set uses :TYPE-PRESCRIPTION rules it will intersect all
; the known type-sets for term.

(defun find-runed-type-prescription (rune lst)

; Lst must be a list of type-prescription rules.  We find the first
; one with :rune rune.

  (cond ((null lst) nil)
        ((equal rune
                (access type-prescription (car lst) :rune))
         (car lst))
        (t (find-runed-type-prescription rune (cdr lst)))))

; Warning: All functions listed above must be defun'd non-recursively
; before deftheory definition-minimal-theory!

; There has been some thought about whether we should put IFF on this
; list.  We have decided not, because type-set knows a lot about it by
; virtue of its being an equivalence relation.  But this position has
; never been seriously scrutinized.

; In a break with nqthm, we have decided to let type-set expand some
; function applications to get better type-sets for them.  The
; functions in question are those listed above.

; In an even more pervasive break, we have decided to make type-set
; keep track of the dependencies between literals of the goal clause
; and the type-sets computed.  The ttree argument to type-set below is
; a running accumulator that is returned as the second value of
; type-set.  Among the tags in the ttree are 'pt tags.  The value of
; the tag is a "parent tree" indicating the set of literals of the
; current-clause upon which the type deduction depends.  See the Essay
; on Parent Trees.  The type-alist in general contains entries of the
; form (term ts . ttree), where ttree is the tag-tree encoding all of
; the 'PTs upon which depend the assertion that term has type-set ts.

; Note on Performance:

; An early time trial detected no measurable difference between the
; old type-set and the new when the ttree is t.  This was on a
; collection of simple defuns and thms (flatten, mc-flatten, their
; relation, and a guarded defun of (assoc-eq2 x y alist) where alist
; is a true list of triples of the form (sym1 sym2 . val)) that
; required a total of 15 seconds run-time in both versions.  However,
; because the only available "old" ACL2 is the first release, which
; does not have all of the proof techniques in place, and the new
; system does have them in place, it is difficult to make meaningful
; tests.  To make matters worse, we are about to go implement forward
; chaining.  The bottom line is whether ACL2 is fast enough.  We'll
; see...

; We now continue with the development of type-set.

(defun mv-atf (not-flg mbt mbf tta fta ttree1 ttree2)

; Every exit of assume-true-false is via this function.  See assume-
; true-false for details.  It is convenient, and only mildly wrong, to
; think of this function as equivalent to:

; (mv mbt mbf tta fta (cons-tag-trees ttree1 ttree2)).

; This is incorrect on two counts.  First, if not-flg is true, we swap
; the roles of mbt/mbf and tta/fta.  Second, since the ttree result of
; assume-true-false is irrelevant unless mbt or mbf is t, we sometimes
; produce a nil ttree.

; The reason this function takes two ttrees is that many (but not all)
; paths through assume-true-false have two ttrees in hand at the end.
; One is the ``xttree'' arg of assume-true-false, which was to be
; included in all the ttrees generated by the function.  The other is
; some local ttree that describes the derivation of facts during
; assume-true-false.  We could combine these two trees before calling
; mv-atf but that would, possibly, waste a cons since the ttrees are
; sometimes ignored.

; Finally, because we know that the ttrees are ignored when mbt and
; mbf are both nil, we sometimes pass in nil for the two ttrees in
; calls of mv-atf where we know they will be ignored.  Such a call
; should be taken (by the reader) as a clear signal that the ttrees
; are irrelevant.

  (if not-flg
      (mv mbf mbt fta tta
          (if (or mbt mbf)
              (cons-tag-trees ttree1 ttree2)
              nil))
      (mv mbt mbf tta fta
          (if (or mbt mbf)
              (cons-tag-trees ttree1 ttree2)
              nil))))

(defun assume-true-false-error (type-alist x temp-temp)
  (er
   hard 'assume-true-false-error
   "It was thought impossible for an equivalence relation, e.g., ~x0, ~
    to have anything besides a non-empty proper subset of ~
    *ts-boolean* on the type-alist!  But in the type-alist ~x1 the ~
    term ~x2 has type set ~x3."
   (ffn-symb x) type-alist x temp-temp))

(defun non-cons-cdr (term)
  (cond ((variablep term) term)
        ((fquotep term) term)
        ((eq (ffn-symb term) 'cons)
         (non-cons-cdr (fargn term 2)))
        (t term)))

; Because type-set now uses type-prescription rules with general
; patterns in them (rather than Nqthm-style rules for function
; symbols), we need one-way unification or pattern matching.

; One-way-unify1 can "see" (binary-+ 1 x) in 7, by letting x be 6.  Thus, we
; say that binary-+ is an "implicit" symbol to one-way-unify1.  Here is the
; current list of implicit symbols.  This list is used for heuristic reasons.
; Basically, a quick necessary condition for pat to one-way-unify with term is
; for the function symbols of pat (except for the implicit ones) to be a subset
; of the function symbols of term.

(defconst *one-way-unify1-implicit-fns*
  '(binary-+
    binary-*
    unary--
    unary-/
    intern-in-package-of-symbol
    coerce
    cons))

(defun one-way-unify1-quotep-subproblems (pat term)

; Caution:  If you change the code below, update
; *one-way-unify1-implicit-fns*.

; Term is a quotep.  This function returns (mv pat1 term1 pat2 term2) as
; follows.  If pat1 is t then pat/s = term for every substitution s, where here
; and below, = denotes provable equality (in other words, it is a theorem in
; the given context that pat = term).  If pat1 is nil then there are no
; requirements.  Otherwise pat1 and term1 are terms and the spec is as follows.
; If pat2 is nil then for every substitution s, pat/s = term if pat1/s = term1.
; But if pat2 is non-nil; then pat2 and term2 are terms, and pat/s = term/s if
; both pat1/s = term1/s and pat2/s = term2/s.

; Thus, this function allows us to reduce the problem of matching pat to a
; quotep, term, to one or two matching problems for "parts" of pat and term.

; In order to prevent loops, we insist that one-way-unification does not
; present the rewriter with ever-more-complex goals.  Robert Krug has sent the
; following examples, which motivated the controls in the code for binary-+ and
; binary-* below.

;  (defstub foo (x) t)
;  (defaxiom foo-axiom
;    (equal (foo (* 2 x))
;           (foo x)))
;  (thm
;   (foo 4))
;  :u
;  (defaxiom foo-axiom
;    (equal (foo (+ 1 x))
;           (foo x)))
;  (thm
;    (foo 4))

; Another interesting example is (thm (foo 4)) after replacing the second
; foo-axiom with (equal (foo (+ -1 x)) (foo x)).

  (declare (xargs :guard (and (pseudo-termp pat)
                              (nvariablep pat)
                              (not (fquotep pat))
                              (pseudo-termp term)
                              (quotep term))))
  (let ((evg (cadr term)))
    (cond ((acl2-numberp evg)
           (let ((ffn-symb (ffn-symb pat)))
             (case ffn-symb
               (binary-+
                (cond ((quotep (fargn pat 1))
                       (let ((new-evg (- evg (fix (cadr (fargn pat 1))))))
                         (cond
                          ((<= (acl2-count new-evg)
                               (acl2-count evg))
                           (mv (fargn pat 2) (kwote new-evg) nil nil))
                          (t (mv nil nil nil nil)))))
                      ((quotep (fargn pat 2))
                       (let ((new-evg (- evg (fix (cadr (fargn pat 2))))))
                         (cond ((<= (acl2-count new-evg)
                                    (acl2-count evg))
                                (mv (fargn pat 1) (kwote new-evg) nil nil))
                               (t (mv nil nil nil nil)))))
                      (t (mv nil nil nil nil))))
               (binary-*
                (cond ((or (not (integerp evg))
                           (int= evg 0))
                       (mv nil nil nil nil))
                      ((and (quotep (fargn pat 1))
                            (integerp (cadr (fargn pat 1)))
                            (> (abs (cadr (fargn pat 1))) 1))
                       (let ((new-term-evg (/ evg (cadr (fargn pat 1)))))
                         (cond ((integerp new-term-evg)
                                (mv (fargn pat 2) (kwote new-term-evg)
                                    nil nil))
                               (t (mv nil nil nil nil)))))
                      ((and (quotep (fargn pat 2))
                            (integerp (cadr (fargn pat 2)))
                            (> (abs (cadr (fargn pat 2))) 1))
                       (let ((new-term-evg (/ evg (cadr (fargn pat 2)))))
                         (cond ((integerp new-term-evg)
                                (mv (fargn pat 1) (kwote new-term-evg)
                                    nil nil))
                               (t (mv nil nil nil nil)))))
                      (t (mv nil nil nil nil))))

; We once were willing to unify (- x) with 3 by binding x to -3.  John Cowles'
; experience with developing ACL2 arithmetic led him to suggest that we not
; unify (- x) with any constant other than negative ones.  Similarly, we do not
; unify (/ x) with any constant other than those between -1 and 1.  The code
; below reflects these suggestions.

               (unary-- (cond ((>= (+ (realpart evg)
                                      (imagpart evg))
                                   0)
                               (mv nil nil nil nil))
                              (t (mv (fargn pat 1) (kwote (- evg)) nil nil))))
               (unary-/ (cond ((or (>= (* evg (conjugate evg))
                                       1)
                                   (eql 0 evg))
                               (mv nil nil nil nil))
                              (t (mv (fargn pat 1) (kwote (/ evg)) nil nil))))
               (otherwise (mv nil nil nil nil)))))
          ((symbolp evg)
           (cond
            ((eq (ffn-symb pat) 'intern-in-package-of-symbol)

; We are unifying 'pkg::name with (intern-in-package-of-symbol x y).  Suppose
; that x is unified with "name"; then when is (intern-in-package-of-symbol
; "name" y) equal to pkg::name?  It would suffice to unify y with any symbol in
; pkg.  It might be that y is already such a quoted symbol.  Or perhaps we
; could unify y with pkg::name, which is one symbol we know is in pkg.  But
; note that it is not necessary that y unify with a symbol in pkg.  It would
; suffice, for example, if y could be unified with a symbol in some other
; package, say gkp, with the property that pkg::name was imported into gkp, for
; then gkp::name would be pkg::name.  Thus, as is to be expected by all failed
; unifications, failure does not mean there is no instance that is equal to the
; term.  Suppose that y is not a quoted symbol and is not a variable (which
; could therefore be unified with pkg::name).  What else might unify with "any
; symbol in pkg?"  At first sight one might think that if y were
; (intern-in-package-of-symbol z 'pkg::name2) then the result is a symbol in
; pkg no matter what z is.  (The idea is that one might think that
; (intern-in-package-of-symbol z 'pkg::name2) is "the" generic expression of
; "any symbol in pkg.")  But that is not true because for certain z it is
; possible that the result isn't in pkg.  Consider, for example, the
; possibility that gkp::zzz is imported into pkg so that if z is "ZZZ" the
; result is a symbol in gkp not pkg.

             (let ((pkg (symbol-package-name evg))
                   (name (symbol-name evg)))
               (cond
                ((and (nvariablep (fargn pat 2))
                      (fquotep (fargn pat 2)))
                 (cond
                  ((symbolp (cadr (fargn pat 2)))
                   (if (equal pkg
                              (symbol-package-name (cadr (fargn pat 2))))
                       (mv (fargn pat 1) (kwote name) nil nil)
                     (mv nil nil nil nil)))
                  (t

; (intern-in-package-of-symbol x y) is NIL if y is not a symbol.  So we win if
; term is 'nil and lose otherwise.  If we win, note that x is unified
; (unnecessarily) with "NIL" in alist1 and so we report the win with alist!  If
; we lose, we have to report alist to be a no change loser.  So it's alist
; either way.

                   (mv (eq evg nil) nil nil nil))))
                (t (mv (fargn pat 1) (kwote name) (fargn pat 2) term)))))
            (t (mv nil nil nil nil))))
          ((stringp evg)
           (cond ((and (eq (ffn-symb pat) 'coerce)
                       (equal (fargn pat 2) ''string))
                  (mv (fargn pat 1) (kwote (coerce evg 'list)) nil nil))
                 (t (mv nil nil nil nil))))
          ((consp evg)
           (cond ((eq (ffn-symb pat) 'cons)

; We have to be careful with alist below so we are a no change loser.

                  (mv (fargn pat 1) (kwote (car evg))
                      (fargn pat 2) (kwote (cdr evg))))
                 (t (mv nil nil nil nil))))
          (t (mv nil nil nil nil)))))

(mutual-recursion

(defun one-way-unify1 (pat term alist)

; Warning: Keep this in sync with one-way-unify1-term-alist.

; This function is a "No-Change Loser" meaning that if it fails and returns nil
; as its first result, it returns the unmodified alist as its second.

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (alistp alist))))
  (cond ((variablep pat)
         (let ((pair (assoc-eq pat alist)))
           (cond (pair (cond ((equal (cdr pair) term)
                              (mv t alist))
                             (t (mv nil alist))))
                 (t (mv t (cons (cons pat term) alist))))))
        ((fquotep pat)
         (cond ((equal pat term) (mv t alist))
               (t (mv nil alist))))
        ((variablep term) (mv nil alist))
        ((fquotep term)

; We have historically attempted to unify ``constructor'' terms with explicit
; values, and we try to simulate that here, treating the primitive arithmetic
; operators, intern-in-package-of-symbol, coerce (to a very limited extent),
; and, of course, cons, as constructors.

         (mv-let
          (pat1 term1 pat2 term2)
          (one-way-unify1-quotep-subproblems pat term)
          (cond ((eq pat1 t) (mv t alist))
                ((eq pat1 nil) (mv nil alist))
                ((eq pat2 nil) (one-way-unify1 pat1 term1 alist))
                (t

; We are careful with alist to keep this a no change loser.

                 (mv-let (ans alist1)
                         (one-way-unify1 pat1 term1 alist)
                         (cond ((eq ans nil) (mv nil alist))
                               (t (mv-let
                                   (ans alist2)
                                   (one-way-unify1 pat2 term2 alist1)
                                   (cond (ans (mv ans alist2))
                                         (t (mv nil alist)))))))))))
        ((cond ((flambda-applicationp pat)
                (equal (ffn-symb pat) (ffn-symb term)))
               (t
                (eq (ffn-symb pat) (ffn-symb term))))
         (cond ((eq (ffn-symb pat) 'equal)
                (one-way-unify1-equal (fargn pat 1) (fargn pat 2)
                                      (fargn term 1) (fargn term 2)
                                      alist))
               (t (mv-let (ans alist1)
                          (one-way-unify1-lst (fargs pat) (fargs term) alist)
                          (cond (ans (mv ans alist1))
                                (t (mv nil alist)))))))
        (t (mv nil alist))))

(defun one-way-unify1-lst (pl tl alist)

; Warning: Keep this in sync with one-way-unify1-term-alist-lst.

; This function is NOT a No Change Loser.  That is, it may return nil
; as its first result, indicating that no substitution exists, but
; return as its second result an alist different from its input alist.

  (declare (xargs :guard (and (pseudo-term-listp pl)
                              (pseudo-term-listp tl)
                              (alistp alist))))
  (cond ((null pl) (mv t alist))
        (t (mv-let (ans alist)
             (one-way-unify1 (car pl) (car tl) alist)
             (cond
              (ans
               (one-way-unify1-lst (cdr pl) (cdr tl) alist))
              (t (mv nil alist)))))))

(defun one-way-unify1-equal1 (pat1 pat2 term1 term2 alist)

; At first glance, the following code looks more elaborate than
; necessary.  But this function is supposed to be a No Change Loser.
; The first time we coded this we failed to ensure that property.  The
; bug is the result of fuzzy thinking in the vicinity of conjunctive
; subgoals.  Suppose success requires success on x and success on y.
; The naive way to code it is (mv-let (ans nochanger) x (if ans y (mv
; nil nochanger))), i.e., to solve the x problem and if you win,
; return your solution to the y problem.  But if x wins it will have
; changed nochanger.  If y then loses, it returns the changed
; nochanger produced by x.  Clearly, if x might win and change things
; but ultimate success also depends on y, you must preserve the
; original inputs and explicitly revert to them if y loses.

  (mv-let (ans alist1)
    (one-way-unify1 pat1 term1 alist)
    (cond (ans
           (mv-let (ans alist2)
                   (one-way-unify1 pat2 term2 alist1)
                   (cond (ans (mv ans alist2))
                         (t (mv nil alist)))))
          (t (mv nil alist)))))

(defun one-way-unify1-equal (pat1 pat2 term1 term2 alist)
  (mv-let (ans alist)
    (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)
    (cond
     (ans (mv ans alist))
     (t (one-way-unify1-equal1 pat2 pat1 term1 term2 alist)))))
)

(defun one-way-unify (pat term)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term))))

; This function returns two values.  The first is T or NIL, according to
; whether unification succeeded.  The second value returned is a symbol alist
; that when substituted into pat will produce term, when the unification
; succeeded.

; The use of the phrase ``unify'' here is somewhat opaque but is
; historically justified by its usage in nqthm.  Really, all we are
; doing is matching because we do not treat the ``variable symbols''
; in term as instantiable.

; Note that the fact that this function returns nil should not be
; taken as a sign that no substitution makes pat equal to term in the
; current theory.  For example, we fail to unify (+ x x) with '2 even
; though '((x . 1)) does the job.

  (one-way-unify1 pat term nil))

; Essay on the Invariants on Type-alists, and Canonicality

; There are four invariants on type-alists.

; First invariant on type-alists:  No quotep is bound in a type-alist.

; Second invariant on type-alists:  when (equiv x y) is bound in a type-alist,
; it is bound to a type of *ts-t* or *ts-nil*.

; Unlike the first two invariants, we will not depend on the third and fourth
; for soundness.  We'll present them in a moment.  We will maintain them both
; by insisting that the only operations allowed for extending type-alists are
; extend-type-alist-simple, extend-type-alist, extend-type-alist1, and
; extend-type-alist-with-bindings, and zip-variable-type-alist, called in
; accordance with their guards.

; Definition.  We say that a term u is "canonical" for an equivalence relation
; equiv of the current ACL2 world and a type-alist if no entry in type-alist is
; of the form ((equiv u z) *ts-t* . ttree).  When equiv and type-alist are
; understood, we may say simply that u is canonical.

; Third invariant on type-alists: For every element ((equiv x y) ts . ttree) of
; a type-alist for which equiv is an equivalence relation in the current ACL2
; world, y is canonical.  Moreover, if ts is *ts-nil*, then x is also
; canonical; and, if ts is *ts-t*, then (term-order y x) and x is not y.
; Finally, for each x there is at most one entry in type-alist of the form
; ((equiv x y) *ts-t* . ttree); in this case, or when x = y and there is no
; entry of the form ((equiv y y') *ts-t* . ttree), we say that y is the
; canonical form of x.

; Although we have decided to maintain the third invariant, if later we decide
; not to be insistent on that, we may obtain some speed-up by replacing some
; calls of extend-type-alist by extend-type-alist-simple.  Look for the string
; ";;*** -simple" to see some places where that might be especially
; appropriate.  Note that even extend-type-alist-simple is careful to preserve
; the first two invariants.

; The fourth invariant on type-alists:  No term is ever bound to *ts-unknown*.

(defun canonical-representative (equiv term type-alist)

; This function returns a tuple (mv occursp canonicalp term-canon ttree)
; satisfying the following description.

; Occursp holds iff, for some x, (equiv term x) or (equiv x term) is bound in
; type-alist.

; Canonicalp is t or nil, and it is t iff term is canonical (see Essay above).

; Term-canon is the canonical form of term, i.e., is term if canonicalp is t
; and otherwise is the unique x such that ((equiv term x) *ts-t* . tt) belongs
; to type-alist for some tt.

; Ttree is a tag-tree justifying the equality of term to term-canon.

; We will use the following easy-to-prove theorem:

; (occursp = nil)
;   implies
; (canonicalp = t)
;   which implies
; (term-canon = term)

; We will also use the fact that if canonicalp is t then ttree is nil.

  (declare (xargs :guard (symbolp equiv)))
  (cond
   ((null type-alist)
    (mv nil t term nil))
   (t (let ((first-term (caar type-alist))
            (ts (cadar type-alist)))
        (cond ((or (variablep first-term)

; Recall the first invariant on type-alists:  type-alists do not bind quoteps.

                   (not (eq (ffn-symb first-term) equiv)))
               (canonical-representative equiv term (cdr type-alist)))
              ((equal term (fargn first-term 1))
               (cond ((ts= ts *ts-t*)
                      (mv t nil (fargn first-term 2) (cddar type-alist)))
                     (t (mv t t term nil))))
              ((equal term (fargn first-term 2))
               (mv t t term nil))
              (t (canonical-representative equiv term (cdr type-alist))))))))

(defun subst-type-alist1-check (old equiv type-alist)
  (cond
   ((null type-alist)
    nil)
   (t (or (let ((term (caar type-alist)))
            (and (ffn-symb-p term equiv)
                 (or (equal old (fargn term 1))
                     (equal old (fargn term 2)))))
          (subst-type-alist1-check old equiv (cdr type-alist))))))

(defun nil-fn ()

; This trivial definition is used for making a sort of placeholder entry,
; *nil-fn-ts-entry*, when simplifying type-alists.  See subst-type-alist1.

  (declare (xargs :guard t :mode :logic))
  nil)

(defconst *nil-fn-ts-entry*
  (list* (cons-term 'nil-fn nil)
         *ts-nil*
         (push-lemma '(:definition nil-fn) nil)))

(defun subst-type-alist1 (new old equiv ttree type-alist acc)

; This subsidiary function of subst-type-alist is coded so that we do not do
; any more consing than necessary.  Moreover, we expect it to be extremely rare
; that old and new are already related (and hence negatively so) by equiv in
; type-alist; someone is calling this function to create such a relationship.

; See also the comment in subst-type-alist.

  (cond
   ((null type-alist)
    (reverse acc))
   (t
    (subst-type-alist1
     new old equiv ttree (cdr type-alist)
     (let ((term (caar type-alist)))
       (cond
        ((and (ffn-symb-p term equiv)
              (or (equal old (fargn term 1))
                  (equal old (fargn term 2))))

; Note that since subst-type-alist1 is only called by subst-type-alist, and
; subst-type-alist assumes that new and old are canonical in type-alist and
; distinct, we know that the third invariant on type-alists is being preserved:
; we are not creating an entry binding (equiv new new) to *ts-t*.

         (let ((equiv-call (if (equal old (fargn term 1))
                               (cons-term* equiv new (fargn term 2))
                             (cons-term* equiv (fargn term 1) new))))
           (cond
            ((quotep equiv-call)

; If we keep this entry, we will violate the first invariant on type-alists.
; But our algorithm for infect-new-type-alist-entries depends on not dropping
; entries!  So we add a silly entry instead.  We could have simply retained the
; existing entry, but this way we can see nil-fn explicitly during debugging,
; and we can contemplate cleaning up the type-alist to remove this specific
; entry.  Why not simply drop the entry entirely?  The problem is that
; subfunctions of assume-true-false make the assumption that they extend the
; type-alist; see infect-new-type-alist-entries.

; It is tempting to check that we're not losing a contradiction, and at one
; time we made check such a check by asserting:

;   (equal (ts= (cadar type-alist) *ts-nil*)
;          (equal equiv-call *nil*))

; But in fact, once we started using type-alist-reducible-entry to strengthen
; assume-true-false(-bc), we found that this check could fail!  This isn't
; surprising: a contradiction could be logically present in a type-alist, but
; not exposed until simplifying it.  We simply add *nil-fn-ts-entry* even in
; that case.

             (cons *nil-fn-ts-entry* acc))
            (t
             (cons (list* equiv-call
                          (cadar type-alist)

; Note on Tracking Equivalence Runes: If we ever give runic names to the
; theorems establishing equivalence- relation-hood and track those names
; through geneqvs, then we ought to push the appropriate rune here, rather than
; use puffert, which was intended for primitives and is thus here somewhat
; misused unless perhaps equiv is 'equal.  There are many other places where
; this comment applies.  You should inspect every use of puffert below and ask
; the question: is equivalential reasoning happening here or is it really
; primitive type reasoning?  We added a function equivalence-rune to record
; commutativity in bdd processing, and this function may be of use here.

                          (puffert
                           (cons-tag-trees (cddar type-alist) ttree)))
                   acc)))))
        (t (cons (car type-alist) acc))))))))

(defun subst-type-alist (new old equiv ttree type-alist)

; This function creates a new type-alist by replacing each term of the form
; (equiv old x) bound in type-alist by (equiv new x), and each remaining term
; of the form (equiv x old) bound in type-alist by (equiv x new), respectively.
; Each time it makes such a replacement it records ttree as the reason why that
; step is valid.

; We assume that new and old are canonical in type-alist and distinct.

  (cond
   ((subst-type-alist1-check old equiv type-alist)
    (subst-type-alist1 new old equiv ttree type-alist nil))
   (t type-alist)))

(defun infect-type-alist-entry (entry ttree)

; Entry is of the form (term ts . ttree1) and we add ttree to ttree1.

  (cons (car entry)
        (cons (cadr entry)
              (cons-tag-trees (cddr entry) ttree))))

(defun infect-new-type-alist-entries2 (new-type-alist old-type-alist ttree)

; We infect the newly modified entries in new-type-alist.  See
; infect-new-type-alist-entries.

  (cond ((null new-type-alist)
         nil)
        ((equal (caar new-type-alist)
                (caar old-type-alist))
         (cons (car new-type-alist)
               (infect-new-type-alist-entries2 (cdr new-type-alist)
                                               (cdr old-type-alist)
                                               ttree)))
        (t
         (cons (infect-type-alist-entry (car new-type-alist) ttree)
               (infect-new-type-alist-entries2 (cdr new-type-alist)
                                               (cdr old-type-alist)
                                               ttree)))))

(defun infect-new-type-alist-entries1 (new-type-alist old-type-alist ttree n)

; We infect the newly created entries in new-type-alist.  See
; infect-new-type-alist-entries.

  (if (zp n)
      (infect-new-type-alist-entries2 new-type-alist old-type-alist
                                      ttree)
    (cons (infect-type-alist-entry (car new-type-alist) ttree)
          (infect-new-type-alist-entries1 (cdr new-type-alist)
                                          old-type-alist
                                          ttree (1- n)))))

(defun infect-new-type-alist-entries (new-type-alist old-type-alist ttree)

; New type-alist is an extension of old-type-alist, and ttree
; contains any assumptions made while deriving the extension.  We
; need to infect the new entries with these assumptions.  This is
; made slightly more complex by the fact that new-type-alist may
; actually be an extension of a modification of old-type-alist
; due to equality facts being added.  (See extend-type-alist1.)
; However, that modification is still in 1:1 correspondence with the
; original, i.e., there are no new entries, just modified entries.

  (if (null ttree)
      new-type-alist
    (infect-new-type-alist-entries1 new-type-alist
                                    old-type-alist
                                    ttree
                                    (- (length new-type-alist)
                                       (length old-type-alist)))))

(defun extend-type-alist-simple (term ts ttree type-alist)

; This function extends type-alist, essentially by adding the entry (term ts .
; ttree).  However, this function preserves the first two invariants on
; type-alists; see the "Essay on the Invariants on Type-alists, and
; Canonicality."  See also extend-type-alist, which is similar but also
; preserves the third invariant on type-alists.

; This function should never be called on a term that is a call of an
; equivalence relation.  When viewed that way, it trivially preserves the third
; invariant on type-alists as well.

  (cond
   ((ts= ts *ts-unknown*) type-alist)
   ((variablep term)
    (cons (list* term ts ttree) type-alist))
   ((fquotep term) type-alist)
   (t (cons (list* term ts ttree) type-alist))))

(defun extend-type-alist1 (equiv occursp1 occursp2 both-canonicalp arg1-canon
                                 arg2-canon swap-flg term ts ttree type-alist)

; This function creates a type-alist in which, intuitively, we bind the term
; (equiv arg1-canon arg2-canon) to ts unless the order is "wrong", in which
; case we use (equiv arg2-canon arg1-canon) instead.

; More precisely, it returns a type-alist that is implied by the current
; type-alist together with the assertion that (equiv arg1-canon arg2-canon) has
; type-set ts, under the following assumptions:

; equiv is an equivalence relation in the current ACL2 world;

; (equiv arg1-canon arg2-canon) is the same as term when (and (not swap-flg)
; both-canonicalp) is non-nil;

; swap-flg is non-nil iff (term-order arg1-canon arg2-canon);

; occurs1p and arg1-canon are returned by some single call of the function
; canonical-representative;

; occurs2p and arg2-canon are returned by some single call of the function
; canonical-representative;

; arg1-canon and arg2-canon are canonical in type-alist (by the two preceding
; assumptions) and distinct.  This is important for the correctness of the
; calls of subst-type-alist; and

; ts is either *ts-t* or *ts-nil*.

  (cons (cond ((and (not swap-flg) both-canonicalp)

; Then term is the term to push on type-alist; no need to cons up a new term.

               (list* term ts ttree))
              (swap-flg (list* (cons-term* equiv arg2-canon arg1-canon)
                               ts (puffert ttree)))
              (t (list* (cons-term* equiv arg1-canon arg2-canon)
                        ts (puffert ttree))))
        (cond ((ts= ts *ts-nil*) type-alist)
              (swap-flg (cond
                         (occursp2

; It's easy to see that occursp2 holds if arg2-canon is an argument of an equiv
; term bound in type-alist, even without assuming that type-alist satisfies the
; third invariant on type-alists.  Hence if occurs2p fails, there is no
; substituting to be done.

                          (subst-type-alist arg1-canon arg2-canon equiv ttree
                                            type-alist))
                         (t type-alist)))
              (t (cond
                  (occursp1

; See comment above for the entirely analogous situation when swap-flg = t.

                   (subst-type-alist arg2-canon arg1-canon equiv ttree
                                     type-alist))
                  (t type-alist))))))

; Regarding the maintenance of the second invariant on type alists:
; In the case that

;   (and (not (ts= ts *ts-t*))
;        (not (ts= ts *ts-nil*))
;        (equivalence-relationp (ffn-symb term) wrld))

; we used to return an unchanged type-alist when extending a type-alist.
; However, we already implicitly use (I think) the fact that equivalence
; relations are boolean-valued.  So, we will do just a bit better in the new
; code.

; Certain violations of the Second invariant on type-alists -- when (equiv x y)
; is bound in a type-alist, it is bound to a type of *ts-t* or *ts-nil* -- is
; reported in assume-true-false by the error function assume-true-false-error,
; which has caught an error in the past.  See the "Essay on the Invariants on
; Type-alists, and Canonicality."

(defun extend-type-alist (term ts ttree type-alist wrld)

; This function extends type-alist so that term gets type-set ts with the
; indicated ttree.  Unlike extend-type-alist-simple, it pays careful attention
; to equivalence relations in an attempt to maintain the third invariant on
; type-alists; see the "Essay on the Invariants on Type-alists, and
; Canonicality."

  (declare (xargs :guard (and (pseudo-termp term)
                              (not (quotep term)))))
  (cond
   ((and (nvariablep term)
         (not (fquotep term))
         (equivalence-relationp (ffn-symb term) wrld))
    (cond
     ((equal (fargn term 1) (fargn term 2))

; It's bizarre to imagine (ts= ts *ts-t*) being false here, so we'll ignore the
; information we could obtain if it were false.

      type-alist)
     ((not (or (ts= ts *ts-t*)
               (ts= ts *ts-nil*)))
      (cond ((ts-intersectp ts *ts-nil*)
             type-alist)
            (t (extend-type-alist
                term *ts-t* (puffert ttree) type-alist wrld))))
     (t (let ((equiv (ffn-symb term))
              (arg1 (fargn term 1))
              (arg2 (fargn term 2)))
          (mv-let (occursp1 canonicalp1 arg1-canon ttree1)
                  (canonical-representative equiv arg1 type-alist)
                  (mv-let (occursp2 canonicalp2 arg2-canon ttree2)
                          (canonical-representative equiv arg2 type-alist)
                          (cond
                           ((equal arg1-canon arg2-canon)
                            type-alist)
                           (t
                            (let ((swap-flg (term-order arg1-canon
                                                        arg2-canon)))
                              (extend-type-alist1
                               equiv occursp1 occursp2
                               (and canonicalp1 canonicalp2)
                               arg1-canon arg2-canon
                               swap-flg
                               term ts
                               (cons-tag-trees ttree1
                                               (cons-tag-trees ttree2 ttree))
                               type-alist))))))))))
   (t (extend-type-alist-simple term ts ttree type-alist))))

(defun zip-variable-type-alist (vars pairs)

; Vars must be a list of distinct variables.  Pairs must be a list of the
; same length as vars, pairing type-sets to ttrees.  This function is
; like (pairlis$ vars pairs) except that it deletes any binding to *ts-unknown*.
; Under the guards stated, we guarantee the result is a type-alist satisfying
; our invariants.

  (cond ((null vars) nil)
        ((ts= (caar pairs) *ts-unknown*)
         (zip-variable-type-alist (cdr vars) (cdr pairs)))
        (t (cons (cons (car vars) (car pairs))
                 (zip-variable-type-alist (cdr vars) (cdr pairs))))))

(defun assoc-equiv (fn arg1 arg2 alist)

; This function is equivalent to
; (or (assoc-equal (list fn arg1 arg2) alist)
;     (assoc-equal (list fn arg2 arg1) alist))
; except that it looks for both at the same time and returns whichever
; one it finds first.  We assume that the car of each pair in
; alist is a non-quote term.

  (cond ((eq alist nil) nil)
        ((and (ffn-symb-p (caar alist) fn)
              (if (equal (fargn (caar alist) 2) arg2)
                  (equal (fargn (caar alist) 1) arg1)
                (and (equal (fargn (caar alist) 1) arg2)
                     (equal (fargn (caar alist) 2) arg1))))
         (car alist))
        (t (assoc-equiv fn arg1 arg2 (cdr alist)))))

(defun assoc-equiv+ (equiv arg1 arg2 type-alist)

; This function body closely parallels code in the 'equal and
; equivalence-relationp cases of assume-true-false.

  (cond
   ((equal arg1 arg2)
    (mv *ts-t* (puffert nil)))
   ((and (eq equiv 'equal) (quotep arg1) (quotep arg2))
    (mv *ts-nil* (push-lemma '(:executable-counterpart equal) nil)))
   (t
    (mv-let
     (occursp1 canonicalp1 arg1-canon ttree1)
     (canonical-representative equiv arg1 type-alist)
     (declare (ignore canonicalp1))
     (cond
      ((and occursp1 (equal arg1-canon arg2))
       (mv *ts-t* (puffert ttree1)))
      ((and occursp1 (eq equiv 'equal) (quotep arg1-canon) (quotep arg2))
       (mv *ts-nil* (push-lemma '(:executable-counterpart equal) ttree1)))
      (t
       (mv-let
        (occursp2 canonicalp2 arg2-canon ttree2)
        (canonical-representative equiv arg2 type-alist)
        (declare (ignore canonicalp2))
        (cond
         ((and occursp2 (equal arg1-canon arg2-canon))
          (mv *ts-t* (puffert (cons-tag-trees ttree1 ttree2))))
         ((and (eq equiv 'equal) occursp2 (quotep arg1-canon) (quotep arg2-canon))
          (mv *ts-nil* (push-lemma '(:executable-counterpart equal)
                                   (cons-tag-trees ttree1 ttree2))))
         (t
          (let ((temp-temp
                 (assoc-equiv equiv arg1-canon arg2-canon type-alist)))
            (cond
             (temp-temp
              (cond ((ts= (cadr temp-temp) *ts-t*)

; See comment in corresponding place in the 'equal case of assume-true-false.

                     (mv (er hard 'assoc-equiv+
                             "Please send the authors of ACL2 a replayable ~
                              transcript of this problem if possible, so that ~
                              they can see what went wrong in the function ~
                              assoc-equiv+.  The offending call was ~x0.  The ~
                              surprising type-set arose from a call of ~x1."
                             (list 'assoc-equiv+
                                   (kwote equiv) (kwote arg1) (kwote arg2)
                                   type-alist)
                             (list 'assoc-equiv
                                   (kwote equiv)
                                   (kwote arg1-canon) (kwote arg2-canon)
                                   '<same_type-alist>))
                         nil))
                    ((ts= (cadr temp-temp) *ts-nil*)
                     (mv *ts-nil* (cons-tag-trees
                                   (cddr temp-temp)
                                   (cons-tag-trees ttree1 ttree2))))
                    (t
                     (let ((erp (assume-true-false-error
                                 type-alist
                                 (mcons-term* equiv arg1-canon arg2-canon)
                                 (cadr temp-temp))))
                       (mv erp nil)))))
             (t (mv nil nil)))))))))))))

(defun assoc-type-alist (term type-alist wrld)
  (cond ((variablep term)
         (let ((temp (assoc-eq term type-alist)))
           (if temp
               (mv (cadr temp) (cddr temp))
             (mv nil nil))))
        ((fquotep term) (mv nil nil))
        ((equivalence-relationp (ffn-symb term) wrld)
         (assoc-equiv+ (ffn-symb term)
                       (fargn term 1)
                       (fargn term 2)
                       type-alist))
        (t (let ((temp (assoc-equal term type-alist)))
             (if temp
                 (mv (cadr temp) (cddr temp))
               (mv nil nil))))))

(defun look-in-type-alist (term type-alist wrld)
  (mv-let (ts ttree)
    (assoc-type-alist term type-alist wrld)
    (mv (if ts ts *ts-unknown*) ttree)))

(defun member-char-stringp (chr str i)
  (declare (xargs :guard (and (stringp str)
                              (integerp i)
                              (< i (length str)))
                  :measure (nfix (+ 1 i))))
  (cond ((not (mbt (integerp i)))
         nil)
        ((< i 0) nil)
        (t (or (eql chr (char str i))
               (member-char-stringp chr str (1- i))))))

(defun terminal-substringp1 (str1 str2 max1 max2)
  (declare (xargs :guard (and (stringp str1)
                              (stringp str2)
                              (integerp max1)
                              (integerp max2)
                              (< max1 (length str1))
                              (< max2 (length str2))
                              (<= max1 max2))
                  :measure (nfix (+ 1 max1))))
  (cond ((not (mbt (integerp max1)))
         nil)
        ((< max1 0) t)
        ((eql (char str1 max1) (char str2 max2))
         (terminal-substringp1 str1 str2 (1- max1) (1- max2)))
        (t nil)))

(defun terminal-substringp (str1 str2 max1 max2)
  (declare (xargs :guard (and (stringp str1)
                              (stringp str2)
                              (integerp max1)
                              (integerp max2)
                              (< max1 (length str1))
                              (< max2 (length str2)))))
  (cond ((< max2 max1) nil)
        (t (terminal-substringp1 str1 str2 max1 max2))))

(defun evg-occur (x y)

; Consider the idealized inductive construction of the ACL2 objects x and y as
; described in the comment for var-fn-count.  Imagine that x and y are so
; represented.  Then this function answers the question: "Does x occur in y?".
; This function is only used heuristically, so we are allowed to deviate from
; the above-mentioned induction construction.

; A comment had been here for a long time up through Version  3.2.1, asking if
; we have to look into symbol-package-names too.  This function is only used
; heuristically, so we choose not to modify it at this time.

  (declare (xargs :guard t))
  (cond ((atom y)
         (cond ((characterp y) (and (characterp x) (eql x y)))
               ((stringp y)
                (cond ((characterp x)
                       (member-char-stringp x y (1- (length y))))
                      ((stringp x)
                       (terminal-substringp x y
                                            (1- (length x))
                                            (1- (length y))))
                      (t nil)))
               ((symbolp y)
                (cond ((characterp x)
                       (let ((sny (symbol-name y)))
                         (member-char-stringp x sny (1- (length sny)))))
                      ((stringp x)
                       (let ((sny (symbol-name y)))
                         (terminal-substringp x sny
                                              (1- (length x))
                                              (1- (length sny)))))
                      ((symbolp x) (eq x y))
                      (t nil)))
               ((integerp y)
                (and (integerp x)
                     (or (int= x y)
                         (and (<= 0 x)
                              (<= x (if (< y 0) (- y) y))))))
               ((rationalp y)

; We know y is a non-integer rational.  X occurs in it either because
; x is the same non-integer rational or x is an integer that occurs in
; the numerator or denominator.

                (cond ((integerp x)
                       (or (evg-occur x (numerator y))
                           (evg-occur x (denominator y))))
                      ((rationalp x) (= x y))
                      (t nil)))
               ((complex-rationalp y)

; We know y is a complex rational.  X occurs in it either because
; x is the same complex rational or x is a rational that occurs in
; the real or imaginary part.

                (cond ((rationalp x)
                       (or (evg-occur x (realpart y))
                           (evg-occur x (imagpart y))))
                      ((complex-rationalp x) (= x y))
                      (t nil)))
               (t (er hard? 'evg-occur
                      "Surprising case:  ~x0"
                      `(evg-occur ,x ,y)))))
        (t (or (evg-occur x (car y))
               (evg-occur x (cdr y))))))

(mutual-recursion

(defun occur (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (cond ((variablep term2)
         (eq term1 term2))
        ((fquotep term2)
         (cond ((quotep term1)
                (evg-occur (cadr term1) (cadr term2)))
               (t nil)))
        ((equal term1 term2) t)
        (t (occur-lst term1 (fargs term2)))))

(defun occur-lst (term1 args2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-term-listp args2))))
  (cond ((endp args2) nil)
        (t (or (occur term1 (car args2))
               (occur-lst term1 (cdr args2))))))
)

; Rockwell Addition:  I found an exponential explosion in worse-than
; and it is fixed here.

; Up through Version  2.5 worse-than was defined as shown below:

; (defun worse-than (term1 term2)
;   (cond ((quick-worse-than term1 term2) t)
;         ((variablep term1) nil)
;         ((fquotep term1) nil)
;         (t (worse-than-lst (fargs term1) term2))))

; But we discovered via Rockwell examples that this performs terribly
; if term1 and term2 are variants of each other, i.e., the same up to
; the variables used.  So we have implemented a short circuit.

(mutual-recursion

(defun pseudo-variantp (term1 term2)

; We determine whether term1 and term2 are identical up to the
; variables used, down to the variables in term1.

; If (pseudo-variantp term1 term2) is true then we know that
; (worse-than term1 term2) is nil.

; Note: In the theorem proving literature, the word ``variant'' is
; used to mean that the two terms are identical up to a renaming of
; variables.  That is checked by our function variantp.  This function
; is different and of little logical use.  It does not insist that a
; consistent renaming of variable occur, just that the two terms are
; isomorphic down to the variable symbols.  It is here to avoid a very
; bad case in the worse-than check.

  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (cond ((variablep term1)

; Suppose that term1 is a variable.  The only thing that it can be
; worse than is a quote.  That is, if we return t, then we must ensure
; that either term2 is term1 or (worse-than term1 term2) is nil.  The
; worse-than will be nil unless term2 is a quote.  See the exponential
; sequences below.

         (not (quotep term2)))

        ((fquotep term1) (equal term1 term2))
        ((or (variablep term2)
             (fquotep term2))
         nil)
        (t (and (equal (ffn-symb term1) (ffn-symb term2))
                (pseudo-variantp-list (fargs term1) (fargs term2))))))

(defun pseudo-variantp-list (args1 args2)
  (declare (xargs :guard (and (pseudo-term-listp args1)
                              (pseudo-term-listp args2))))
  (cond ((endp args1) t)
        (t (and (pseudo-variantp (car args1) (car args2))
                (pseudo-variantp-list (cdr args1) (cdr args2)))))))

; It turns out that without the use of pseudo-variantp in the
; definition of worse-than, below, worse-than's cost grows
; exponentially on pseudo-variant terms.  Consider the sequence of
; terms (f a a), (f a (f a a)), ..., and the corresponding sequence
; with variable symbol b used in place of a.  Call these terms a1, a2,
; ..., and b1, b2, ...  Then if pseudo-variantp were redefined to
; return nil, here are the real times taken to do (worse-than a1 b1),
; (worse-than a2 b2), ...:  0.000, 0.000, 0.000, 0.000, 0.000, 0.000,
; 0.000, 0.020, 0.080, 0.300, 1.110, 4.230, 16.390.  This was measured
; on a 330 MHz Pentium II.

; (progn
;   (time
;    (new-worse-than
;     '(f a a)
;     '(f b b)))
;
;   (time
;    (new-worse-than
;     '(f a (f a a))
;     '(f b (f b b))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a a)))
;     '(f b (f b (f b b)))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a a))))
;     '(f b (f b (f b (f b b))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a a)))))
;     '(f b (f b (f b (f b (f b b)))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a a))))))
;     '(f b (f b (f b (f b (f b (f b b))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a a)))))))
;     '(f b (f b (f b (f b (f b (f b (f b b)))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a a))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b b))))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
;
;   (time
;    (new-worse-than
;     '(f a
;         (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))))
;     '(f b
;         (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
;
;   (time
;    (new-worse-than
;     '(f a
;         (f a
;            (f a
;               (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))))
;     '(f b
;         (f b
;            (f b
;               (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
;     ))
;   )

; If pseudo-variantp is defined so that instead of (not (quotep
; term2)) it insists of (variablep term2) when (variablep term1), then
; the following sequence goes exponential even though the preceding
; one does not.

; (progn
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))))
;     ))
;   )

; with times of 0.000, 0.120, 0.250, 0.430, etc.  But with the current
; definition of pseudo-variantp, the sequence above is flat.

; However, the sequence with the terms commuted grows exponentially,
; still.

; (progn
;   (time
;    (new-worse-than
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))
;
;   (time
;    (new-worse-than
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))
;
;   (time
;    (new-worse-than
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))
;
;   (time
;    (new-worse-than
;     '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f b
;         (f b
;            (f b
;               (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f b
;         (f b
;            (f b
;               (f b
;                  (f b
;                     (f b
;                        (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f b
;         (f b
;            (f b
;               (f b
;                  (f b
;                     (f b
;                        (f b
;                           (f b
;                              (f b
;                                 (f b (f b (f b (f b (f b (f b b)))))))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f b
;         (f b
;            (f b
;               (f b
;                  (f b
;                     (f b
;                        (f b
;                           (f b
;                              (f b
;                                 (f b
;                                    (f b
;                                       (f b
;                                          (f b (f b (f b (f b b))))))))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     ))
;
;   (time
;    (new-worse-than
;     '(f b
;         (f b
;            (f b
;               (f b
;                  (f b
;                     (f b
;                        (f b
;                           (f b
;                              (f b
;                                 (f b
;                                    (f b
;                                       (f b
;                                          (f b
;                                             (f b
;                                                (f b
;                                                   (f b
;                                                      (f b b)))))))))))))))))
;     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
;     ))
;   )

; Real times: 0.000, 0.000, 0.010, 0.000, 0.010, 0.020, 0.040, 0.100,
; 0.210, ...

(defmacro decrement-worse-than-clk (clk)
  (declare (xargs :guard (symbolp clk)))
  `(if (< ,clk 2) ,clk (1-f ,clk)))

(defmacro with-decrement-worse-than-clk (clk form)
  (declare (xargs :guard (symbolp clk)))
  `(let ((,clk (decrement-worse-than-clk ,clk)))
     (declare (type (unsigned-byte 29) ,clk))
     ,form))

(defmacro worse-than-builtin-clocked-body (clk)

; This is simply a way to share code between worse-than-builtin-clocked and
; worse-than-builtin-memoized.

  (declare (xargs :guard (atom clk))) ; avoid repeated evaluation of clk
  `(cond
    ((basic-worse-than term1 term2 ,clk) t)
    ((pseudo-variantp term1 term2) nil)
    ((variablep term1)

; If term1 is a variable and not basic-worse-than term2, what do we know about
; term2?  Term2 might be a variable.  Term2 cannot be quote.  Term2 might be a
; function application.  So is X worse-than-builtin X or Y or (F X Y)?  No.

     nil)
    ((fquotep term1)

; If term1 is a quote and not basic-worse-than term2, what do we know about
; term2?  Term2 might be a variable.  Also, term2 might be a quote, but if it
; is, term2 is bigger than term1.  Term2 might be a function application.  So
; is term1 worse-than-builtin a bigger quote?  No.  Is term1 worse-than-builtin
; a variable or function application?  No.

     nil)
    (t (worse-than-lst (fargs term1) term2 ,clk))))

(mutual-recursion

; Comment on memoizing a worse-than function: A way to do so is to uncomment
; the following definition and take other actions described with the comment
; "Comment on memoizing a worse-than function".
; (defun worse-than-builtin-memoized (term1 term2)
;   (declare
;    (xargs :guard (and (pseudo-termp term1)
;                       (pseudo-termp term2))
;           :measure (make-ord 1
;                              (+ 1 (acl2-count term1) (acl2-count term2))
;                              1)
;           :well-founded-relation o<))
;   (worse-than-builtin-clocked-body 0))

(defun worse-than-builtin-clocked (term1 term2 clk)

; Term1 is worse-than-builtin term2 if it is basic-worse-than term2 or some
; proper subterm of it is worse-than-builtin or equal to term2.  However, we
; know that if two terms are pseudo-variants of each other, then the
; worse-than-builtin relation does not hold.

; This use of a clocked function is new after Version_7.0.  Our investigations
; into the worse-than heuristic after that release began with an email from
; Camm Maguire on Jan. 21, 2015, pointing out that books/coi/dtrees/base.lisp
; was the only book that required more than 2G memory for certification using
; ACL2(h) 7.0 built on 64-bit GCL.  We found the memoization of
; worse-than-builtin was the culprit.  An email discussion with Jared Davis
; included his suggestion of a clocked version, rather like this one, that
; avoided the use of memoization until reaching a sufficient recursion depth.
; It occurred to us that with a clocked version, perhaps memoization could be
; avoided entirely, possibly saving memory and leading to a simpler, arguably
; more predictable implementation.  Comments below explore these options.

  (declare
   (type (unsigned-byte 29) clk)
   (xargs :guard (and (pseudo-termp term1)
                      (pseudo-termp term2))
          :measure (make-ord 1
                             (+ 1 (acl2-count term1) (acl2-count term2))
                             2)
          :well-founded-relation o<))
  (cond
   ((zpf clk)

; We are out of "time".  The following three options are available:

; Comment on memoizing a worse-than function: To change whether or how that is
; done, visit the comments below and also search for other comments labeled
; with "Comment on memoizing a worse-than function".

; (1) Return nil, with the intention that although our "worse-than" code may be
; incomplete, still it should imply some sort of true worse-than.

    nil

; (2) Return t (an idea put forth by Jared Davis), the idea being that if we
; get to this point, then big terms are involved and if worse-than is intended
; to defeat some process, then it is reasonable to do so in this case.

;   t

; (3) Continue, but using memoization as had been done in Version_7.0.

;   (worse-than-builtin-memoized term1 term2)

; We did a number of experiments in late January, 2015, after the release of
; Version_7.0.  Major results are reported below.  In short, all three
; approaches improved the performance, with differences perhaps in the noise.
; It was a close call, but we decided against (3) since its added complexity
; and possible memory usage didn't seem to provide non-trivial value, and we
; decided on (1) over (2) because (1) had less risk of destroying existing
; proofs (albeit with the risk that, unlike (2), some proofs might loop that
; otherwise would not because of a weaker ancestors-check.

; All results below used the same unloaded machine/platform (64-bit Linux,
; 3.5 GHz 4-core Intel(R) Xeon(R) with Hyper-Threading), with a command like
; the following.

;   (setenv TIME_CERT yes ; time nice make -j 8 regression-everything \
;    OS_HAS_GLUCOSE= USE_QUICKLISP=1 TB_LISP=gcl ACL2=<my_acl2>)

; CCL results are below, then GCL.

;;; CCL

; original
; Unmodified from the the worse-than implementation in Version_7.0:
; 52692.173u 1924.728s 2:26:28.33 621.4%	0+0k 1209904+5209720io 862pf+0w

; run-1
; No memoization of worse-than-builtin, except in stv2c.lisp:
; 51938.137u 1917.763s 2:22:16.90 630.8%	0+0k 1054112+5206800io 865pf+0w

; run-2
; No memoization of any worse-than-xx, but use clocked version (bottom
; out at nil):
; 52311.357u 1912.043s 2:23:35.01 629.4%	0+0k 841976+5208048io 521pf+0w

; run-3
; No memoization of any worse-than-xx, but use clocked version (bottom
; out at t):
; 52186.933u 1910.623s 2:23:30.81 628.2%	0+0k 835600+5207784io 688pf+0w

; run-4
; No memoization of any worse-than-xx at the top level, but use
; clocked version that bottoms out at a memoized version:
; 51934.529u 1929.868s 2:20:54.27 637.1%	0+0k 1328800+5207736io 939pf+0w

; run-5-try1
; As just above, but clearing memo tables only between proofs (had
; tried to do so as in Jared's scheme but had a bug) -- so should be
; much like run-4:
; 51968.175u 1876.825s 2:23:26.50 625.6%	0+0k 1378000+5207784io 984pf+0w

; run-5
; As in run-4, but clearing memo tables as per Jared's scheme, not
; just between proofs.
; 52139.274u 1908.239s 2:22:38.12 631.5%	0+0k 1537656+5207808io 1120pf+0w

;;; GCL

; original
; Unmodified from the the worse-than implementation in Version_7.0:
; 63181.644u 1732.384s 2:39:00.22 680.4%	0+0k 7886424+10142248io 6495pf+0w

; run-2
; No memoization of any worse-than-xx, but use clocked version (bottom
; out at nil):
; 62302.405u 1732.200s 2:36:22.51 682.4%	0+0k 7585424+10141528io 6709pf+0w

; run-3
; No memoization of any worse-than-xx, but use clocked version (bottom
; out at t) -- done kind of late in the game, so might not correspond
; exactly to run-3 for ccl, but should be close:
; 62325.511u 1752.913s 2:40:06.65 667.0%	0+0k 7911496+10141232io 6432pf+0w

; run-4
; No memoization of any worse-than-xx at the top level, but use
; clocked version that bottoms out at a memoized version:
; 62211.735u 1773.406s 2:42:14.22 657.3%	0+0k 7263696+9823120io 6140pf+0w

; run-5-try1
; As just above, but clearing memo tables only between proofs (had
; tried to do so as in Jared's scheme but had a bug) -- so should be
; much like run-4:
; 62414.848u 1681.773s 2:38:58.45 671.9%	0+0k 6878536+9799112io 5834pf+0w

; run-5
; As in run-4, but clearing memo tables as per Jared's scheme, not
; just between proofs.
; 62541.228u 1765.406s 2:38:42.69 675.2%	0+0k 6730944+9798968io 5749pf+0w

    )

; Comment on memoizing a worse-than function: In order to memoize according to
; scheme (3) above, uncomment the following code.

;  ((eql clk 1)
;   (let ((ans (worse-than-builtin-memoized term1 term2)))
;     (prog2$ (clear-memoize-table 'worse-than-builtin-memoized)
;             ans)))

   (t (let ((clk (1-f clk)))
        (declare (type (unsigned-byte 29) clk))
        (worse-than-builtin-clocked-body clk)))))

(defun worse-than-or-equal-builtin-clocked (term1 term2 clk)

; This function is not really mutually recursive and could be removed from this
; nest.  It determines whether term1 is term2 or worse than term2.  This nest
; defines worse-than-builtin and does not use this function despite the use of
; similarly named functions.

; Note:  This function is supposed to be equivalent to
; (or (equal term1 term2) (worse-than-builtin term1 term2)).

; Clearly, that is equivalent to

; (if (pseudo-variantp term1 term2)
;     (or (equal term1 term2) (worse-than-builtin term1 term2))
;     (or (equal term1 term2) (worse-than-builtin term1 term2)))

; But if pseudo-variantp is true, then worse-than-builtin must return nil.  And
; if pseudo-variantp is nil, then the equal returns nil.  So we can simplify
; the if above to:

  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))
                  :measure (make-ord 1
                                     (+ 1
                                        (acl2-count term1)
                                        (acl2-count term2))
                                     3)
                  :well-founded-relation o<))
  (if (pseudo-variantp term1 term2)
      (equal term1 term2)
    (worse-than-builtin-clocked term1 term2 (decrement-worse-than-clk clk))))

(defun basic-worse-than-lst1 (args1 args2 clk)

; Is some element of args2 ``uglier'' than the corresponding element of args1.
; Technically, a2 is uglier than a1 if a1 is atomic (a variable or constant)
; and a2 is not or a2 is worse-than-builtin a1.

  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-term-listp args1)
                              (pseudo-term-listp args2))
                  :measure
                  (make-ord 1 (+ 1 (acl2-count args1) (acl2-count args2)) 0)
                  :well-founded-relation o<))
  (cond ((endp args1) nil)
        ((or (and (or (variablep (car args1))
                      (fquotep (car args1)))
                  (not (or (variablep (car args2))
                           (fquotep (car args2)))))
             (worse-than-builtin-clocked (car args2)
                                         (car args1)
                                         clk))
         t)
        (t (basic-worse-than-lst1 (cdr args1)
                                  (cdr args2)
                                  clk))))

(defun basic-worse-than-lst2 (args1 args2 clk)

; Is some element of arg1 worse-than-builtin the corresponding element of args2?

  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-term-listp args1)
                              (pseudo-term-listp args2))
                  :measure (make-ord 1
                                     (+ 1
                                        (acl2-count args1)
                                        (acl2-count args2))
                                     0)
                  :well-founded-relation o<))
  (cond ((endp args1) nil)
        ((worse-than-builtin-clocked (car args1) (car args2) clk) t)
        (t (basic-worse-than-lst2 (cdr args1) (cdr args2) clk))))

(defun basic-worse-than (term1 term2 clk)

; We say that term1 is basic-worse-than term2 if

; * term2 is a variable and term1 properly contains it, e.g., (F A B)
;   is basic-worse-than A;

; * term2 is a quote and term1 is either not a quote or is a bigger
;   quote, e.g., both X and '124 are basic-worse-than '17 and '(A B C D
;   E) is worse than 'X; or

; * term1 and term2 are applications of the same function and no argument of
;   term2 is uglier than the corresponding arg of term1, and some argument of
;   term1 is worse-than-builtin the corresponding arg of term2.

; The last case is illustrated by the fact that (F A B) is basic-worse-than (F
; A '17), because B is worse than '17, but (F '17 B) is not basic-worse-than (F
; A '17) because A is worse than '17.  Think of term2 as the old goal and term1
; as the new goal.  Do we want to cut off backchaining?  Yes, if term1 is
; basic-worse-than term2.  So would we backchain from (F A '17) to (F '17 B)?
; Yes, because even though one argument (the second) got worse (it went from 17
; to B) another argument (the first) got better (it went from A to 17).

  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))
                  :measure (make-ord 1
                                     (+ 1
                                        (acl2-count term1)
                                        (acl2-count term2))
                                     0)
                  :well-founded-relation o<))
  (cond ((variablep term2)
         (cond ((eq term1 term2) nil)
               (t (occur term2 term1))))
        ((fquotep term2)
         (cond ((variablep term1) t)
               ((fquotep term1)
                (> (fn-count-evg (cadr term1))
                   (fn-count-evg (cadr term2))))
               (t t)))
        ((variablep term1) nil)
        ((fquotep term1) nil)
        ((cond ((flambda-applicationp term1)
                (equal (ffn-symb term1) (ffn-symb term2)))
               (t (eq (ffn-symb term1) (ffn-symb term2))))
         (cond ((pseudo-variantp term1 term2) nil)
               (t (with-decrement-worse-than-clk
                   clk
                   (cond ((basic-worse-than-lst1 (fargs term1)
                                                 (fargs term2)
                                                 clk)
                          nil)
                         (t (basic-worse-than-lst2 (fargs term1)
                                                   (fargs term2)
                                                   clk)))))))
        (t nil)))

(defun some-subterm-worse-than-or-equal (term1 term2 clk)

; Returns t if some subterm of term1 is worse-than-builtin or equal to term2.

  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))
                  :measure (make-ord 1
                                     (+ 1
                                        (acl2-count term1)
                                        (acl2-count term2))
                                     1)
                  :well-founded-relation o<))
  (cond
   ((variablep term1) (eq term1 term2))
   (t (with-decrement-worse-than-clk
       clk
       (cond
        ((if (pseudo-variantp term1 term2) ; see worse-than-or-equal-builtin-clocked
             (equal term1 term2)
           (basic-worse-than term1 term2 clk))
         t)
        ((fquotep term1) nil)
        (t (some-subterm-worse-than-or-equal-lst (fargs term1)
                                                 term2
                                                 clk)))))))

(defun some-subterm-worse-than-or-equal-lst (args term2 clk)
  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-term-listp args)
                              (pseudo-termp term2))
                  :measure (make-ord 1
                                     (+ 1 (acl2-count args) (acl2-count term2))
                                     0)
                  :well-founded-relation o<))
  (cond
   ((endp args) nil)
   (t (or (some-subterm-worse-than-or-equal (car args) term2 clk)
          (some-subterm-worse-than-or-equal-lst (cdr args) term2 clk)))))

(defun worse-than-lst (args term2 clk)

; We determine whether some element of args contains a subterm that is
; worse-than-builtin or equal to term2.  The subterm in question may be the
; element of args itself.  That is, we use ``subterm'' in the ``not necessarily
; proper subterm'' sense.

  (declare (type (unsigned-byte 29) clk)
           (xargs :guard (and (pseudo-term-listp args)
                              (pseudo-termp term2))
                  :measure (make-ord 1
                                     (+ 1 (acl2-count args) (acl2-count term2))
                                     0)
                  :well-founded-relation o<))
  (cond ((endp args) nil)
        (t (or (some-subterm-worse-than-or-equal (car args) term2 clk)
               (worse-than-lst (cdr args) term2 clk)))))

)

(encapsulate
 ((worse-than
   (term1 term2) t
   :guard
   (and (pseudo-termp term1)
        (pseudo-termp term2))))
 (local (defun worse-than (term1 term2)
          (declare (ignore term1 term2)
                   nil))))
(encapsulate
 ((worse-than-or-equal
   (term1 term2) t
   :guard
   (and (pseudo-termp term1)
        (pseudo-termp term2))))
 (local (defun worse-than-or-equal (term1 term2)
          (declare (ignore term1 term2)
                   nil))))

(defmacro worse-than-clk () 15)

(defun worse-than-builtin (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (worse-than-builtin-clocked term1 term2 (worse-than-clk)))

(defun worse-than-or-equal-builtin (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (worse-than-or-equal-builtin-clocked term1 term2 (worse-than-clk)))

(defattach (worse-than worse-than-builtin)
  :skip-checks t)

(defattach (worse-than-or-equal worse-than-or-equal-builtin)
  :skip-checks t)

; Begin treatment of the ancestors stack.

(defrec ancestor

; Note: if lit is :binding-hyp, then atm is hyp, fn-count is unify-subst and
; tokens is nil (see relevant comment in earlier-ancestor-biggerp).  See
; make-ancestor-binding-hyp, ancestor-binding-hyp-p, ancestor-binding-hyp/hyp,
; and ancestor-binding-hyp/unify-subst.

; Bkptr is the one-based number of the hypothesis that generated this ancestor,
; in the case that the hypothesis is not a binding hypothesis.  Otherwise bkptr
; is nil.

; To obtain the literals from a list of ancestors, call
; strip-ancestor-literals.  (Strip-cars will still work at this time, but we do
; not guarantee that in the future.)

  (lit atm var-cnt fn-cnt p-fn-cnt tokens . bkptr)
  t)

(defmacro make-ancestor-binding-hyp (hyp unify-subst)
  `(make ancestor
         :lit :binding-hyp
         :atm ,hyp
         :var-cnt ,unify-subst
         :tokens nil
         :bkptr nil))

(defmacro ancestor-binding-hyp-p (anc)
  `(eq (access ancestor ,anc :lit)
       :binding-hyp))

(defmacro ancestor-binding-hyp/hyp (anc)
  `(access ancestor ,anc :atm))

(defmacro ancestor-binding-hyp/unify-subst (anc)
  `(access ancestor ,anc :var-cnt))

; Here is how we add a frame to the ancestors stack.

(defun push-ancestor (lit tokens ancestors bkptr)

; This function is used to push a new pair onto ancestors.  Lit is a term to be
; assumed true.  Tokens is a list of arbitrary objects.  Generally, tokens is a
; singleton list containing the rune of a rule through which we are
; backchaining.  But when we rewrite forced assumptions we use the ``runes''
; from the assumnotes (see defrec assumnote) as the tokens.  These ``runes''
; are not always runes but may be symbols.

; Bkptr is nil unless we are relieving a hypothesis other than a binding
; hypothesis, in which case it is the one-based index of that hypothesis.

; Note: It is important that the literal, lit, be in the car of the frame
; constructed below.

  (let* ((alit lit)
         (alit-atm (mv-let (not-flg atm)
                           (strip-not alit)
                           (declare (ignore not-flg))
                           atm)))
    (mv-let
     (var-cnt-alit-atm fn-cnt-alit-atm p-fn-cnt-alit-atm)
     (var-fn-count alit-atm nil)
     (cons (make ancestor
                 :lit alit ; the literal being assumed true (negation of hyp!)
                 :atm alit-atm               ; the atom of that literal
                 :var-cnt var-cnt-alit-atm   ; the var-count of that atom
                 :fn-cnt fn-cnt-alit-atm     ; the fn-count of that atom
                 :p-fn-cnt p-fn-cnt-alit-atm ; the pseudo-fn-count of that atom
                 :tokens tokens ; the runes involved in this backchain
                 :bkptr bkptr) ; for the hypothesis (see comment above)
           ancestors))))

(defun ancestor-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        ((not (weak-ancestor-p (car x)))
         nil)
        ((ancestor-binding-hyp-p (car x))
         (and

; See relevant comment in earlier-ancestor-bigger for why :tokens must be nil
; in this case.

          (null (access ancestor (car x) :tokens))
          (ancestor-listp (cdr x))))
        (t (let* ((anc (car x))
                  (alit (access ancestor anc :lit))
                  (alit-atm (access ancestor anc :atm))
                  (var-cnt-alit-atm (access ancestor anc :var-cnt))
                  (fn-cnt-alit-atm (access ancestor anc :fn-cnt))
                  (p-fn-cnt-alit-atm (access ancestor anc :p-fn-cnt))
                  (atokens (access ancestor anc :tokens)))
             (and (pseudo-termp alit)
                  (pseudo-termp alit-atm)
                  (integerp var-cnt-alit-atm)
                  (integerp fn-cnt-alit-atm)
                  (integerp p-fn-cnt-alit-atm)
                  (true-listp atokens)
                  (ancestor-listp (cdr x)))))))

(defun earlier-ancestor-biggerp (var-cnt fn-cnt p-fn-cnt tokens ancestors)

; We return t if some ancestor on ancestors has a bigger fn-count than
; fn-cnt and intersects with tokens.

  (declare (xargs :guard (and (integerp var-cnt)
                              (integerp fn-cnt)
                              (integerp p-fn-cnt)
                              (true-listp tokens)
                              (ancestor-listp ancestors))))
  (cond ((endp ancestors) nil)
        (t (let* ((anc (car ancestors))
                  (var-cnt-alit-atm (access ancestor anc :var-cnt))
                  (fn-cnt-alit-atm (access ancestor anc :fn-cnt))
                  (p-fn-cnt-alit-atm (access ancestor anc :p-fn-cnt))
                  (atokens (access ancestor anc :tokens)))
             (cond ((and (intersectp-equal tokens atokens)

; (Car ancestors) might specify an ancestor-binding-hyp-p.  In this case some
; of the values compared below using < are nil.  However, those comparisons do
; not take place because in this case atokens is also nil, so the
; intersectp-equal test above returns nil.

                         (var-or-fn-count-< var-cnt var-cnt-alit-atm
                                            fn-cnt fn-cnt-alit-atm
                                            p-fn-cnt p-fn-cnt-alit-atm))
                    t)
                   (t (earlier-ancestor-biggerp var-cnt fn-cnt p-fn-cnt tokens
                                                (cdr ancestors))))))))

(defun equal-mod-commuting (x y wrld)

; If this function returns t, then either x and y are the same term, or they
; are provably equal by virtue of the commutativity of their common binary
; function symbol.

; Recall that we do not track the use of equivalence relations; so we do not
; report their use here.  When we do that, read the Note on Tracking
; Equivalence Runes in subst-type-alist1.

  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (plist-worldp wrld))))
  (cond ((variablep x)
         (eq x y))
        ((variablep y)
         nil)
        ((or (fquotep x) (fquotep y))
         nil) ; quotes are handled elsewhere
        ((equal x y)
         t)
        ((flambdap (ffn-symb x))
         nil)
        (t (let ((fnx (ffn-symb x)))
             (and (eq fnx (ffn-symb y))
                  (if (member-eq fnx '(equal iff)) ; optimization
                      t
                    (and wrld ; optimization
                         (equivalence-relationp fnx wrld)))
                  (equal (fargn x 1) (fargn y 2))
                  (equal (fargn x 2) (fargn y 1)))))))

(defun ancestors-check1 (lit-atm lit var-cnt fn-cnt p-fn-cnt ancestors tokens)

; Roughly speaking, ancestors is a list of all the things we can assume by
; virtue of our trying to prove their negations.  That is, when we backchain
; from B to A by applying (implies A B), we try to prove A and so we put (NOT
; A) on ancestors and can legitimately assume it (i.e., (NOT A)) true.  We
; return (mv t on-ancestors) if we determine heuristically that further
; backchaining is inadvisable, where on-ancestors is t if roughly speaking, lit
; is a member-equal of ancestors, and otherwise on-ancestors is nil.  Otherwise
; we return (mv nil nil).

; We implement the complement check as follows.  lit-atm is the atom of the
; literal lit.  Consider a literal of ancestors, alit, and its atom, alit-atm.
; If lit-atm is alit-atm and lit is not equal to alit, then lit and alit are
; complementary.  The following table supports this observation.  It shows all
; the combinations by considering that lit is either a positive or negative p,
; and alit is a p of either sign or some other literal of either sign.  The
; entries labeled = mark those when lit is alit.  The entries labeled comp mark
; those when lit and alit are complementary.

; lit \  alit:    p (not p) q (not q)

; p               =   comp  x    x
; (not p)         comp =    x    x

  (declare (xargs :guard (and (pseudo-termp lit-atm)
                              (pseudo-termp lit)
                              (integerp var-cnt)
                              (integerp fn-cnt)
                              (integerp p-fn-cnt)
                              (ancestor-listp ancestors)
                              (true-listp tokens))))
  (cond
   ((endp ancestors)
    (mv nil nil))
   ((ancestor-binding-hyp-p (car ancestors))
    (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt (cdr ancestors) tokens))
   (t
    (let ((alit              (access ancestor (car ancestors) :lit))
          (alit-atm          (access ancestor (car ancestors) :atm))
          (var-cnt-alit-atm  (access ancestor (car ancestors) :var-cnt))
          (fn-cnt-alit-atm   (access ancestor (car ancestors) :fn-cnt))
          (p-fn-cnt-alit-atm (access ancestor (car ancestors) :p-fn-cnt))
          (atokens           (access ancestor (car ancestors) :tokens)))
      (cond
       ((equal-mod-commuting alit lit nil)

; Here, and in the next branch, we provide the empty world to
; equal-mod-commuting.  If we want a stronger check then we could provide the
; current ACL2 world instead, but then we would have to add a world argument to
; ancestors-check1 and ancestors-check.  As Robert Krug pointed out to us,
; there may be other places in our sources more deserving of generalization
; from 'equal to arbitrary equivalence relations.

; Better yet, we can mark equivalence relations in the ancestors stack, which
; costs a cons each time but may save many getprop calls.

        (mv t t))
       ((equal-mod-commuting lit-atm alit-atm nil) (mv t nil))

; See the comment above, for the preceding call of equal-mod-commuting.

; In Version_2.5, this function did not have the tokens argument.  Instead we
; simply asked whether there was a frame on the ancestors stack such that
; fn-cnt was greater than or equal to the fn-count of the atom in the frame and
; lit-atm was worse-than-or-equal to the atom in the frame.  If so, we aborted
; with (mv t nil).  (The fn-cnt test is just an optimization because that
; inequality is implied by the worse-than-or-equal test.)  But Carlos Pacheco's
; TLA work exposed a situation in which the lit-atm was worse-than-or-equal to
; a completely unrelated atom on the ancestors stack.  So we added tokens and
; insisted that the ancestor so dominated by lit-atm was related to lit-atm by
; having a non-empty intersection with tokens.  This was added in the final
; polishing of Version_2.6.  But we learned that it slowed us down about 10%
; because it allowed so much more backchaining.  We finally adopted a very
; conservative change targeted almost exactly to allow Carlos' example while
; preserving the rest of the old behavior.

       ((intersectp-equal tokens atokens)

; We get here if the current lit-atm is related to that in the current frame.
; We next ask whether the function symbols are the same and lit-atm is bigger.
; If so, we abort.  Otherwise, we look for others.

        (cond ((and (nvariablep alit-atm)
                    (not (fquotep alit-atm))
                    (nvariablep lit-atm)
                    (not (fquotep lit-atm))
                    (equal (ffn-symb lit-atm) (ffn-symb alit-atm))
                    (not (var-or-fn-count-< var-cnt var-cnt-alit-atm
                                            fn-cnt fn-cnt-alit-atm
                                            p-fn-cnt p-fn-cnt-alit-atm)))
               (mv t nil))
              (t (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt
                                   (cdr ancestors) tokens))))
       ((and (not (var-or-fn-count-< var-cnt var-cnt-alit-atm
                                     fn-cnt fn-cnt-alit-atm
                                     p-fn-cnt p-fn-cnt-alit-atm))
             (worse-than-or-equal lit-atm alit-atm))

; The clause above is the old Version_2.5 test, but now it is tried only if the
; atms are unrelated by their tokens.  Most of the time we want to abort
; backchaining if we pass the check above.  But we want to allow continued
; backchaining in Carlos' example.  In that example:

; lit-atm          = (S::MEM (S::APPLY S::DISKSWRITTEN S::P)
;                            (S::POWERSET (S::DISK)))
; fn-cnt           = 4
; alit-atm         = (S::MEM S::D (S::DISK))
; fn-cnt-alit-atm  = 2

; with no token intersection.  Once upon a time we simply allowed all these,
; i.e., just coded a recursive call here.  But that really slowed us down by
; enabling a lot of backchaining.  So now we basically want to ask: "Is there a
; really good reason to allow this backchain?"  We've decided to allow the
; backchain if there is an earlier ancestor, related by tokens, to the ancestor
; that is trying to veto this one, that is bigger than this one.  In Carlos'
; example there is such a larger ancestor; but we suspect most of the time
; there isn't.  For example, at the very least it means that the vetoing
; ancestor must be the SECOND (or subsequent) time we've applied some rule on
; this backchaining path!  The first time we coded this heuristic we named the
; test ``random-coin-flip'' instead of earlier-ancestor-biggerp; the point:
; this is a pretty arbitrary decision heuristic mainly to make Carlos' example
; work.

        (cond ((earlier-ancestor-biggerp var-cnt
                                         fn-cnt
                                         p-fn-cnt
                                         atokens
                                         (cdr ancestors))
               (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt
                                 (cdr ancestors) tokens))
              (t (mv t nil))))
       (t (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt
                            (cdr ancestors) tokens)))))))

; Note: In the type-set clique, and nowhere else, ancestors might be
; t.  The so-called t-ancestors hack is explained below.  But this
; function and push-ancestor above DO NOT implement the t-ancestors
; hack.  That is because they are used by the rewrite clique where
; there is no such hack, and we didn't want to slow that clique down.

(defun ancestors-check-builtin (lit ancestors tokens)

; We return two values.  The first is whether we should abort trying to
; establish lit on behalf of the given tokens.  The second is whether lit is
; (assumed) true in ancestors.

; We abort iff either lit is assumed true or else it is worse than or equal to
; some other literal we're trying to establish on behalf of some token in
; tokens.  (Actually, we compare the atoms of the two literals in the
; worse-than check.)

; A reminder about ancestors: Ancestors is a list of ``frames.''  Each frame is
; of one of two forms.  Most frames are constructed by push-ancestor and have
; the form:

; (lit alit cnt1 cnt2 tokens)

; where lit is a term that may be assumed true in the current context, alit is
; the atom of lit (i.e., with a NOT stripped if necessary), cnt1 and cnt2 are
; the fn- and pseudo-fn counts of alit as computed by fn-count-1, and tokens is
; a true-list of arbitrary objects but most often the runes (or base symbols of
; runes) responsible for back chaining to this frame).

; However, sometimes we push a frame of the form:

; (:BINDING-HYP hyp unify-subst)

; where hyp is of the form (equiv var term) and unify-subst is a substitution
; in which var is free and there are no relatively free vars in term.

; For purposes of guard checking all we assume about ancestors is
; ancestor-listp.

; Historical Note:  In nqthm, this function was named relieve-hyps-not-ok.

  (declare (xargs :guard (and (pseudo-termp lit)
                              (ancestor-listp ancestors)
                              (true-listp tokens))))
  (cond ((endp ancestors)
         (mv nil nil))
        (t (mv-let (not-flg lit-atm)
                   (strip-not lit)
                   (declare (ignore not-flg))
                   (mv-let (var-cnt fn-cnt p-fn-cnt)
                           (var-fn-count lit-atm nil)
                           (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt
                                             ancestors tokens))))))

(defproxy ancestors-check (* * *) => (mv * *))

(defattach (ancestors-check ancestors-check-builtin)
  :skip-checks t)

; Essay on Type-set Deductions for Integerp

; Robert Krug found it disturbing that ACL2 could not make certain type-set
; deductions about whether terms are definitely integers or are definitely not
; integers.  Version_3.2.1 and beyond contains code descended from a
; contribution from Robert (included below through type-set-finish) that
; rectifies this problem, which is illustrated by examples contributed by
; Robert, in community book books/misc/integer-type-set-test.lisp.

; Here is an outline of the issue.  Suppose we have:

; Term to type:
; y  = a+bx   [a and b numeric constants]

; Now suppose we find the following in the type-alist:

; Term typed as definitely integer or definitely not integer:
; y' = a'+b'x [a' constant, b' a non-zero numeric constant]

; Then note:

; y = (a - (ba'/b')) + (b/b')y'.

; Let C = (a - Da') where D = b/b'; so

; y = C + Dy' [where C and D are known to be numeric].

; We can prove the following in order to justify the claim just above:

; (include-book "arithmetic/top" :dir :system)
; (thm (implies (and (equal y (+ a (* b x)))
;                    (equal y2 (+ a2 (* b2 x)))
;                    (acl2-numberp b2) (not (equal b2 0)))
;               (let* ((d (/ b b2))
;                      (c (- a (* d a2))))
;                 (equal y (+ c (* d y2))))))

; Then we can, of course, potentially strengthen the type known for y by using
; the above alternate form of y, combining in a suitable manner the known types
; of y', C, and D.

; The description above is slightly simplistic, however.  Suppose for example
; that y above is 2 + 4u + 6v, while y' is 7 + 10u + 15v.  Then in fact we can
; view y and y' as follows.

; y  = 2 +  4(u + 3/2 v)
; y' = 7 + 10(u + 3/2 v)

; The representation of a term as having the form a+bx is performed by function
; normalize-linear-sum.

; Robert informs us that he tried an analogous enhancement in which one tries
; to decide rationalp propositions in addition to integerp propositions, but he
; found that to be exceedingly expensive.

; We now develop the code for normalize-linear-sum and then the code for
; type-set-finish-1.  The sorting done by normalize-linear-sum-2 was added
; after Version_4.3; an example in normalize-linear-sum illustrates what that
; adds.

; End of Essay on Type-set Deductions for Integerp.

(defun map-multiply-car (multiplicative-constant x)
 (cond ((endp x) nil)
       (t (cons (cons (* multiplicative-constant (car (car x)))
                      (cdr (car x)))
                (map-multiply-car multiplicative-constant (cdr x))))))

(defun normalize-addend (addend)

; Addend is a term.  We return a pair (multiplicative-constant
; . rest-of-addend), where multiplicative-constant is a rational (not a term)
; and rest-of-addend is a term, such that addend = multiplicative-constant *
; rest-of-addend.  The intent is for rest-of-addend to have a coefficient of 1,
; though we do not rely on this for correctness.

  (cond ((variablep addend)
         (cons 1 addend))
        ((fquotep addend)
         (cons 1 addend))
        ((flambda-applicationp addend)
         (cons 1 addend))
        ((eq (ffn-symb addend) 'UNARY--)
         (cons -1 (fargn addend 1)))
        ((eq (ffn-symb addend) 'BINARY-*)
         (cond ((and (quotep (fargn addend 1)) ; Addend is of the form (* a x).
                     (rationalp (unquote (fargn addend 1))))
                (cons (unquote (fargn addend 1)) (fargn addend 2)))
               (t (cons 1 addend))))
        (t
         (cons 1 addend))))

(defun insert-cdr-term-order (item list)
  (cond ((endp list)
         (list item))
        ((term-order (cdr (car list)) (cdr item))
         (cons (car list)
               (insert-cdr-term-order item (cdr list))))
        (t
         (cons item list))))

(defun normalize-linear-sum-2 (term)

; Term is (at least initially) a sum.  We return a list of pairs
; (multiplicative-constant . rest-of-addend), one pair for each addend of term.
; Furthermore, these pairs are sorted by term-order on rest-of-addend.

  (cond ((eq (fn-symb term) 'BINARY-+)
         (insert-cdr-term-order
          (normalize-addend (fargn term 1))
          (normalize-linear-sum-2 (fargn term 2))))
        (t (list (normalize-addend term)))))

(defun normalize-linear-sum-1 (additive-constant term)

; Given a rational number, additive-constant, and a term, we return (mv a b x)
; where: a and b are rational numbers, x is a term (but see below), and
; additive-constant + term = a + b * x.
;
; The preceding is almost correct.  When x would be a sum, it is instead
; represented as a list of pairs --- (multiplicative-constant
; . rest-of-addend), one pair for each addend.  Note that there is no
; possibility for confusion, i.e., if two calls produce the same x, then either
; each x represents a term or each x represents a list of pairs of the form
; above.  To see this, note that if x is a term of the form ((u . v) . w) then
; u is the symbol LAMBDA, not a number:
; (thm (implies (pseudo-termp (cons (cons u v) w)) (equal u 'lambda))).

  (cond ((variablep term)
         (mv additive-constant 1 term))
        ((fquotep term) ; degenerate case; any sound result might be fine
         (cond ((rationalp (unquote term))
                (mv (+ additive-constant (unquote term)) 1 *0*))
               (t
                (mv additive-constant 1 term))))
        ((flambda-applicationp term)
         (mv additive-constant 1 term))
        ((eq (ffn-symb term) 'UNARY--)
         (mv additive-constant -1 (fargn term 1)))
        ((eq (ffn-symb term) 'BINARY-*)
         (cond ((and (quotep (fargn term 1))
                     (rationalp (unquote (fargn term 1))))
                (mv additive-constant (unquote (fargn term 1)) (fargn term 2)))
               (t
                (mv additive-constant 1 term))))
        ((eq (ffn-symb term) 'BINARY-+)
         (let* ((temp-1 (normalize-linear-sum-2 term))

; Temp-1 is a list of pairs --- (multiplicative-constant . rest-of-addend).
; These pairs are sorted by term order on rest-of-addend.

                (multiplicative-constant (car (car temp-1))))
           (cond ((or (eql multiplicative-constant 0) ; degenerate case
                      (eql multiplicative-constant 1))
                  (mv additive-constant 1 temp-1))
                 (t
                  (let ((temp-2
                         (map-multiply-car (/ multiplicative-constant)
                                           temp-1)))
                    (mv additive-constant multiplicative-constant temp-2))))))
        (t
         (mv additive-constant 1 term))))

(defun normalize-linear-sum (term)

; For context, see the Essay on Type-set Deductions for Integerp.  Here, we
; return three values: additive-constant, multiplicative-constant, and
; normalized-term such that

; term = 'additive-constant + 'multiplicative-constant * normalized-term,

; where additive-constant and multiplicative-constant are rational numbers
; (not quoted) and normalized-term has a leading coefficient of 1 or 0.  We
; intend it to be 1, but there is not much we can do with (+ 3 (* 0 x)).
;
; Pseudo examples:
; (foo x) ==> (mv 0 1 (foo x))
; (- (foo x)) ==> (mv 0 -1 (foo x))
; (+ x y) ==> (mv 0 1 (+ x y))
; (+ (* 3 x) y) ==> (mv 0 3 (+ x (* 1/3 y)))
; (+ 2 (* 3 x) y) ==> (mv 2 3 (+ x (* 1/3 y)))
;
; Note that for best results, sums and products must be right-associated with
; the addends/factors in term order (or at least with constants all the way to
; the left), and terms such as (- (* 3 ...)) do not appear.  (* -3 ...) is the
; preferred form.  Robert Krug underwent a process to accommodate terms that do
; not satisfy these assumptions, but he tells us that the code rapidly became
; unwieldy and he found no natural stopping point for that process.

; The following example shows why we sort using normalize-linear-sum-2.
; Without sorting, the conclusion doesn't reduce to (foo t).

; (defstub foo (x) t)
; (thm ; should reduce conclusion to (foo t)
;  (implies (and (rationalp x)
;                (rationalp y)
;                (integerp (+ x (* 1/3 y))))
;           (foo (integerp (+ y (* 3 x))))))

; The following similar example shows why we need to consider terms that aren't
; sums.  As above, that is needed in order for the conclusion to simplify to
; (foo t).

; (thm ; should reduce conclusion to (foo t)
;  (implies (and (rationalp x)
;                (rationalp y)
;                (integerp (* 1/3 y)))
;           (foo (integerp y))))

  (cond ((variablep term)
         (mv 0 1 term))
        ((fquotep term) ; not needed due to the first invariant on type-alists
         (mv 0 1 term))
        ((flambda-applicationp term)
         (mv 0 1 term))
        ((eq (ffn-symb term) 'UNARY--)
         (mv 0 -1 (fargn term 1)))
        ((eq (ffn-symb term) 'BINARY-*)
         (cond ((and (quotep (fargn term 1))
                     (rationalp (unquote (fargn term 1))))
                (mv 0 (unquote (fargn term 1)) (fargn term 2)))
               (t
                (mv 0 1 term))))
        ((eq (ffn-symb term) 'BINARY-+)
         (cond ((and (quotep (fargn term 1))
                     (rationalp (unquote (fargn term 1))))
                (normalize-linear-sum-1 (unquote (fargn term 1))
                                        (fargn term 2)))
               (t
                (normalize-linear-sum-1 0 term))))
        (t
         (mv 0 1 term))))

(defun normalize-linear-sum-p1 (stripped-term term-to-match)
  (cond ((null stripped-term) nil)
        ((ffn-symb-p term-to-match 'BINARY-+)
         (normalize-linear-sum-p1 (cdr stripped-term)
                                  (fargn term-to-match 2)))
        (t (null (cdr stripped-term)))))

(defun normalize-linear-sum-p (stripped-term term-to-match)

; This function is a heuristic filter.  It is desirable to return nil if and
; only if there is clearly no hope that there is a match, using the algorithm
; in type-set-finish-1, between the results of normalizing a given term into (&
; & stripped-term) and the result of normalizing a second term, term-to-match.
; Note that stripped-term is either a term or is an alist associating numbers
; with terms.

  (let ((term ; strip additive constant
         (cond ((and (ffn-symb-p term-to-match 'BINARY-+)
                     (quotep (fargn term-to-match 1)))
                (fargn term-to-match 2))
               (t term-to-match))))
    (cond ((and (consp stripped-term)
                (consp (car stripped-term))
                (acl2-numberp (caar stripped-term)))

; Stripped-term is an alist with entries (number . term).

           (normalize-linear-sum-p1 stripped-term term))
          (t ; Stripped-term is a term.
           (not (ffn-symb-p term 'BINARY-+))))))

(defun type-set-finish-1 (additive-const multiplicative-const stripped-term
                                         ts ttree type-alist)

; For context, see the Essay on Type-set Deductions for Integerp.  Here, we are
; taking the type-set of a term

; x = additive-const + multiplicative-const * stripped-term,

; that is known to be rational, where additive-const and multiplicative-const
; are rational numbers.  We try to tighten the type set, ts, relative to the
; given type-alist, so that x is known to be an integer or known to be a ratio
; (neither of which is known coming into this function).
;
; We scan through the type-alist looking for a typed-term that is known to be
; an integer or known to be a ratio and equal to typed-additive-const +
; typed-multiplicative-const * stripped-term for some typed-additive-const and
; typed-multiplicative-const.  The story continues in the comments below.

  (cond ((null type-alist)
         (mv ts ttree))
        ((and (or (ts-subsetp (cadr (car type-alist)) *ts-integer*)
                  (ts-subsetp (cadr (car type-alist)) *ts-ratio*))
              (normalize-linear-sum-p stripped-term
                                      (car (car type-alist))))
         (let ((term-to-match (car (car type-alist)))
               (type-to-match (cadr (car type-alist)))
               (ttree-to-match (cddr (car type-alist))))
           (mv-let (typed-additive-const
                    typed-multiplicative-const
                    stripped-term-to-match)
                   (normalize-linear-sum term-to-match)
                   (cond
                    ((and (equal stripped-term stripped-term-to-match)
                          (not (eql typed-multiplicative-const 0)))

; We have found a typed-term of the desired form, described above.  We merge
; the constant appropriately --- see the thm and let-binding immediately below.

;  (include-book "arithmetic/top" :dir :system)
;  (thm
;   (implies (and (rationalp additive-const)
;                 (rationalp multiplicative-const)
;                 (rationalp typed-additive-const)
;                 (rationalp typed-multiplicative-const)
;                 (not (equal typed-multiplicative-const 0))
;                 (equal orig-term (+ additive-const
;                                     (* multiplicative-const term)))
;                 (equal typed-term (+ typed-additive-const
;                                      (* typed-multiplicative-const term))))
;            (equal orig-term
;                   (+ (- additive-const
;                         (* multiplicative-const
;                            typed-additive-const
;                            (/ typed-multiplicative-const)))
;                      (* multiplicative-const
;                         (/ typed-multiplicative-const)
;                         typed-term)))))

                     (let* ((merged-multiplicative-const
                             (* multiplicative-const
                                (/ typed-multiplicative-const)))
                            (merged-additive-const
                             (- additive-const
                                (* merged-multiplicative-const
                                   typed-additive-const))))
                       (cond ((and (not (eql merged-additive-const 0))
                                   (not (eql merged-multiplicative-const 1)))
                              (let* ((merged-multiplicative-const-ts
                                      (type-set-quote
                                       merged-multiplicative-const))
                                     (merged-additive-const-ts
                                      (type-set-quote merged-additive-const))

; We have have the following type information:
; ts:
;   type of orig-term (the term we are typing), which intersects both
;   *ts-ratio* and *ts-integer* and is contained in *ts-rational*
; type-to-match:
;   type of the matching term found in the type-alist (the typed-term above)
; merged-multiplicative-const-ts:
;   the type of the merged-multiplicative-const (which is rational)
; merged-additive-const-ts:
;   the type of the merged-additive-const (which is rational)
;
; Furthermore, by construction and the thm above, we know that
; (a) orig-term =
;     merged-additive-const + merged-multiplicative-const * typed-term
;
; We wish to strengthen the type of orig-term, so we compute its type using (a)
; above.  This is done by the calls to aref2 below, which are based on those in
; type-set-binary-* and type-set-binary-+.  We then intersect the newly
; computed type with the original one, ts.  If this final type is strong
; enough, we return.  Otherwise we continue our search.
;
                                     (new-ts1 (aref2 'type-set-binary-*-table
                                                     *type-set-binary-*-table*
                                                     merged-multiplicative-const-ts
                                                     type-to-match))
                                     (new-ts2 (aref2 'type-set-binary-+-table
                                                     *type-set-binary-+-table*
                                                     merged-additive-const-ts
                                                     new-ts1))
                                     (new-ts3 (ts-intersection ts new-ts2)))
                                (if (or (ts-subsetp new-ts3 *ts-integer*)
                                        (ts-subsetp new-ts3 *ts-ratio*))
                                    (mv new-ts3
                                        (puffert
                                         (cons-tag-trees ttree
                                                         ttree-to-match)))
                                  (type-set-finish-1 additive-const
                                                     multiplicative-const
                                                     stripped-term
                                                     ts
                                                     ttree
                                                     (cdr type-alist)))))
                             ((not (eql merged-additive-const 0))

; orig-term = merged-additive-const + typed-term.
;
; This is just like the above, but since merged-multiplicative-const
; is 1, we skip typing merged-multiplicative-const * stripped-term-to-match.

                              (let* ((merged-additive-const-ts
                                      (type-set-quote merged-additive-const))
                                     (new-ts1 (aref2 'type-set-binary-+-table
                                                     *type-set-binary-+-table*
                                                     merged-additive-const-ts
                                                     type-to-match))
                                     (new-ts2 (ts-intersection ts new-ts1)))
                                (if (or (ts-subsetp new-ts2 *ts-integer*)
                                        (ts-subsetp new-ts2 *ts-ratio*))
                                    (mv new-ts2
                                        (puffert (cons-tag-trees ttree
                                                                 ttree-to-match)))
                                  (type-set-finish-1 additive-const
                                                     multiplicative-const
                                                     stripped-term
                                                     ts
                                                     ttree
                                                     (cdr type-alist)))))
                             ((not (eql merged-multiplicative-const 1))

; orig-term = merged-multiplicative-const * typed-term.
;
; Similar to the above, but here we take advantage of the fact that
; merged-additive-const is known to be 0.

                              (let* ((merged-multiplicative-const-ts
                                      (type-set-quote
                                       merged-multiplicative-const))
                                     (new-ts1 (aref2 'type-set-binary-*-table
                                                     *type-set-binary-*-table*
                                                     merged-multiplicative-const-ts
                                                     type-to-match))
                                     (new-ts2 (ts-intersection ts new-ts1)))
                                (if (or (ts-subsetp new-ts2 *ts-integer*)
                                        (ts-subsetp new-ts2 *ts-ratio*))
                                    (mv new-ts2
                                        (puffert (cons-tag-trees ttree
                                                                 ttree-to-match)))
                                  (type-set-finish-1 additive-const
                                                     multiplicative-const
                                                     stripped-term
                                                     ts
                                                     ttree
                                                     (cdr type-alist)))))
                             (t

; orig-term = typed-term
;
; Presumably ts is at least as strong as type-to-match, but at any rate, this
; isn't a case we care to consider, so we simply recur.

                              (type-set-finish-1 additive-const
                                                 multiplicative-const
                                                 stripped-term
                                                 ts
                                                 ttree
                                                 (cdr type-alist))))))
                    (t (type-set-finish-1 additive-const
                                          multiplicative-const
                                          stripped-term
                                          ts
                                          ttree
                                          (cdr type-alist)))))))
        (t (type-set-finish-1 additive-const
                              multiplicative-const
                              stripped-term
                              ts
                              ttree
                              (cdr type-alist)))))

(defun type-set-finish (x ts0 ttree0 ts1 ttree1 type-alist)

; We have obtained two type-set answers for the term x.  Ts0 and ttree0 were
; obtained by looking the term up in the type-alist; if ts0 is nil, then no
; binding was found in the type-alist.  Ts1 and ttree1 were obtained by
; computing the type-set of the term "directly."  Both are valid, provided ts0
; is non-nil.  We intersect them.

; Note: Our answer must include ttree1 because that is the accumulated
; dependencies of the type-set computation to date!

  (mv-let (ts ttree)
          (cond ((null ts0)
                 (mv ts1 ttree1))
                ((ts-subsetp ts1 ts0)

; This is an optimization.  We are about to intersect the type-sets and union
; the tag-trees.  But if ts1 is a subset of ts0, the intersection is just ts1.
; We need not return ttree0 in this case; note that we must always return ttree1.

                 (mv ts1 ttree1))
                (t (mv (ts-intersection ts0 ts1)
                       (cons-tag-trees ttree0 ttree1))))

; See the Essay on Type-set Deductions for Integerp for why we make the
; following, final attempt.

          (cond ((and (ts-subsetp ts *ts-rational*)
                      (ts-intersectp ts *ts-integer*)
                      (ts-intersectp ts *ts-ratio*))
                 (mv-let (additive-const multiplicative-const stripped-term)
                         (normalize-linear-sum x)
                         (type-set-finish-1 additive-const multiplicative-const
                                            stripped-term ts ttree
                                            type-alist)))
                (t
                 (mv ts ttree)))))

(defun search-type-alist-rec (term alt-term typ type-alist unify-subst ttree)
  (cond ((null type-alist)
         (mv nil unify-subst ttree nil))
        ((ts-subsetp (cadr (car type-alist)) typ)
         (mv-let (ans unify-subst)
           (one-way-unify1 term (car (car type-alist)) unify-subst)
           (cond (ans
                  (mv t
                      unify-subst
                      (cons-tag-trees (cddr (car type-alist)) ttree)
                      (cdr type-alist)))
                 (alt-term
                  (mv-let (ans unify-subst)
                    (one-way-unify1 alt-term (car (car type-alist))
                                    unify-subst)
                    (cond (ans
                           (mv t
                               unify-subst
                               (cons-tag-trees (cddr (car type-alist)) ttree)
                               (cdr type-alist)))
                          (t (search-type-alist-rec term alt-term
                                                    typ
                                                    (cdr type-alist)
                                                    unify-subst
                                                    ttree)))))
                 (t (search-type-alist-rec term alt-term
                                           typ
                                           (cdr type-alist)
                                           unify-subst
                                           ttree)))))
        (t (search-type-alist-rec term alt-term
                                  typ
                                  (cdr type-alist)
                                  unify-subst
                                  ttree))))

(mutual-recursion

(defun free-varsp (term alist)
  (cond ((variablep term) (not (assoc-eq term alist)))
        ((fquotep term) nil)
        (t (free-varsp-lst (fargs term) alist))))

(defun free-varsp-lst (args alist)
  (cond ((null args) nil)
        (t (or (free-varsp (car args) alist)
               (free-varsp-lst (cdr args) alist)))))

)

(defun search-type-alist-with-rest (term typ type-alist unify-subst ttree wrld)

; See search-type-alist.

  (mv-let (term alt-term)
    (cond ((or (variablep term)
               (fquotep term)
               (not (equivalence-relationp (ffn-symb term) wrld)))
           (mv term nil))

; Otherwise, term is of the form (equiv term1 term2).  If term1 precedes term2
; in term-order, then term would be stored on a type-alist as (equiv term2
; term1); see the Essay on the Invariants on Type-alists, and Canonicality
; (specifically, the third invariant described there).  In such a case we may
; wish to search for the commuted version instead of term.  However, if there
; are free variables in term with respect to unify-subst then we need to search
; both for term and its commuted version, because the more specific term on
; type-alist can have its arguments in either term-order (unless we engage in a
; relatively expensive check; see e.g. maximal-terms).

          ((free-varsp term unify-subst)
           (mv term
               (fcons-term* (ffn-symb term) (fargn term 2) (fargn term 1))))
          (t (let ((arg1 (fargn term 1))
                   (arg2 (fargn term 2)))
               (cond ((term-order arg1 arg2)
                      (mv (fcons-term* (ffn-symb term)
                                       (fargn term 2)
                                       (fargn term 1))
                          nil))
                     (t (mv term nil))))))
    (search-type-alist-rec term alt-term typ type-alist unify-subst ttree)))

(defun search-type-alist (term typ type-alist unify-subst ttree wrld)

; We search type-alist for an instance of term bound to a type-set
; that is a subset of typ.  Keep this in sync with search-type-alist+.

; For example, if typ is *ts-rational* then we seek an instance of
; term that is known to be a subset of the rationals.  Most commonly,
; typ is *ts-non-nil*.  In that case, we seek an instance of term
; that is non-nil.  Thus, this function can be thought of as trying to
; "make term true."  To use this function to "make term false," use
; the ts-complement of the desired type.  I.e., if you wish to find a
; false instance of term use *ts-nil*.

; By "instance" here we always mean an instance under an extension of
; unify-subst.  The extension is returned when we are successful.

; We return three values.  The first indicates whether we succeeded.
; The second is the final unify-subst.  The third is a modified ttree
; recording the literals used.  If we did not succeed, the second
; and third values are our input unify-subst and ttree.  I.e., we are
; a No-Change Loser.

; The No-Change Policy:  Many multi-valued functions here return a
; flag that indicates whether they "won" or "lost" and, in the case
; that they won, return "new values" for certain of their arguments.
; Here for example, we return a new value for unify-subst.  In early
; coding we adopted the policy that when they "lost" the additional
; values were irrelevant and were often nil.  This policy prevented
; the use of such forms as:
; (mv-let (wonp unify-subst)
;         (search-type-alist ... unify-subst ...)
;         (cond (wonp ...)
;               (t otherwise...)))
; because at otherwise... unify-subst was no longer what it had been before
; the search-type-alist.  Instead we had to think of a new name for
; it in the mv-let and use the appropriate one below.

; We then adopted what we now call the "No-Change Policy".  If a
; function returns a won/lost flag and some altered arguments, the
; No-Change Policy is that it returns its input arguments in case it
; loses.  We will note explicitly when a function is a No-Change
; Loser.

  (mv-let (ans unify-subst ttree rest-type-alist)
          (search-type-alist-with-rest term typ type-alist unify-subst ttree
                                       wrld)
          (declare (ignore rest-type-alist))
          (mv ans unify-subst ttree)))

(defun term-and-typ-to-lookup (hyp wrld ens)
  (mv-let
    (not-flg term)
    (strip-not hyp)
    (let ((recog-tuple (and (nvariablep term)
                            (not (fquotep term))
                            (not (flambda-applicationp term))
                            (most-recent-enabled-recog-tuple
                             (ffn-symb term) wrld ens))))
      (cond ((and recog-tuple
                  (access recognizer-tuple recog-tuple :strongp))
             (mv (fargn term 1)
                 (if not-flg
                     (access recognizer-tuple recog-tuple :false-ts)
                   (access recognizer-tuple recog-tuple :true-ts))
                 (access recognizer-tuple recog-tuple :rune)))
            (t (mv term
                   (if not-flg *ts-nil* *ts-non-nil*)
                   nil))))))

(defun lookup-hyp (hyp type-alist wrld unify-subst ttree ens)

; See if hyp is true by type-alist or simp-clause considerations --
; possibly extending the unify-subst.  If successful we return t, a
; new unify-subst and a new ttree.  No-Change Loser.

  (mv-let (term typ rune)
    (term-and-typ-to-lookup hyp wrld ens)
    (mv-let (ans unify-subst ttree)
      (search-type-alist term typ type-alist unify-subst ttree wrld)
      (mv ans unify-subst (if (and ans rune)
                              (push-lemma rune ttree)
                            ttree)))))

(defun bind-free-vars-to-unbound-free-vars (vars alist)

; For every var in vars that is not bound in alist, create the binding
; (var . UNBOUND-FREE-var) and add that binding to alist.  Return the
; extended alist.  We use this function to instantiate free vars in
; FORCEd and CASE-SPLIT hypotheses.  In that application, vars will be
; the list of all vars occurring in the hyp and alist will be the
; unify-subst.  The name ``unbound free var'' is a little odd out of
; context but we hope it will make the user realize that the variable
; occurred freely and we couldn't find a binding for it to make the hyp
; true before forcing or splitting.

  (cond ((endp vars) alist)
        ((assoc-eq (car vars) alist)
         (bind-free-vars-to-unbound-free-vars (cdr vars) alist))
        (t (bind-free-vars-to-unbound-free-vars
            (cdr vars)
            (cons (cons (car vars)
                        (packn (list 'unbound-free- (car vars))))
                  alist)))))

; Essay on Accumulated Persistence

; We now develop the code needed to track accumulated-persistence.  The
; documentation topic for accumulated-persistence serves as a useful
; introduction to what is implemented by the code, and is a good starting point
; before reading this Essay.

; A typical use of this utility is as follows.

; >(accumulated-persistence t)              ; activate and initialize
; > ...                                     ; do proofs
; >(show-accumulated-persistence :frames)   ; to display stats ordered by
;                                           ;  frame count
; >(accumulated-persistence nil)            ; deactivate

; A macro form is available for use in system code to support the tracking of
; accumulated persistence.  The special-form

; (with-accumulated-persistence rune (v1 ... vk) body)

; should be used in our source code whenever body is code that attempts to
; apply rune.  The list of variables, (v1 ... vk), tell us the multiplicity
; of body.  This form is logically equivalent to

; (mv-let (v1 ... vk) body (mv v1 ... vk))

; which is to say, it is logically equivalent to body itself.  (In the case
; where k is 1, we naturally use a let instead of an mv-let.)  However, we
; insert some additional code to accumulate the persistence of rune.

; There are optional arguments of with-accumulated-persistence not described in
; this essay, but whose meaning is pretty clear from the code.

; The implementation of accumulated-persistence is as follows.  First, the
; necessary global data structures are maintained as the status of a wormhole
; called 'accumulated-persistence.  As usual with a wormhole status, it is of
; the form (:key . data), where :key is either :SKIP or :ENTER indicating
; whether wormhole is supposed to actually enter the wormhole.  The data itself
; is an accp-info record.  The record stores success (useful work) and failure
; (useless work) counts, success and failure stacks, and totals, as follows.
; Conceptually, there is always a current stack for lemmas other than the one
; currently being applied (after push-accp but before pop-accp).  The stack is
; initially empty, but every attempt to apply a lemma (with push-accp) pushes
; current information on the stack and starts accumulating information for that
; lemma, for example while relieving hypotheses.  More precisely, all our data
; is kept in a single accp-info record, which is the value of the wormhole-data
; field of wormhole-status.

; If accumulated persistence is enabled then we give special treatment to
; hypotheses and conclusions of rules.  Each is represented as an ``extended
; rune'' (``xrune''), which provides an accumulation site for work done on
; behalf of that hypothesis or conclusion.  Thus, we actually traffic in
; xrunes, where an xrune is either a rune, a hyp-xrune (:hyp rune , n) where n
; is a positive integer, or a conc-xrune (:conc . rune).  The hyp-xrune (:hyp
; rune . n) is used in accumulated-persistence for recording the work done on
; behalf of the nth hypothesis of rune, while the conc-xrune (:conc . rune)
; records the work done on behalf of the right-hand-side of the rune.  Note
; that :doc accumulated-persistence says that a hyp-xrune is (:hyp n . rune)
; rather than (:hyp rune . n), but we found the latter form much more
; convenient for sorting.  Still, we present (:hyp n . rune) to the user by
; calling prettyify-xrune.

; On recursion

; Through Version_8.2 we overcounted accumulated frames for a rule applied
; recursively, in the sense that it already on the stack discussed above when
; it is again pushed onto the stack.  The problem was documented essentially as
; follows.

;    Consider the following example.
;
;      (defun mem (a x)
;        (if (atom x)
;            nil
;          (or (equal a (car x)) (mem a (cdr x)))))
;
;    Now suppose we consider the sequence of theorems (mem a (list a)),
;    (mem a (list 1 a)), (mem a (list 1 2 a)), (mem a (list 1 2 3 a)),
;    and so on.  We will see that the :frames reported for each
;    increases quadratically, even though the :tries increases linearly;
;    so in this case the :tries statistics are more appropriate.  Each
;    time the definition of mem is applied, a new stack frame is pushed
;    (see [accumulated-persistence]), and all subsequent applications of
;    that definition are accumulated into the :frames count for that
;    stack frame.  The final :frames count will be the sum of the counts
;    for those individual frames, which form a linear sequence whose sum
;    is therefore quadratic in the number of applications of the
;    definition of mem.

; We now avoid this problem by skipping the accumulation of frames for such
; recursive rule applications (though we still count their tries); these will
; be accumulated in full in the top-level applications of the rule.  See the
; variable top-level-p in function pop-accp-fn.

(defabbrev x-xrunep (xrune) ; extended xrunep
  (or (eq (car xrune) :hyp)
      (eq (car xrune) :conc)))

(defabbrev hyp-xrune (n rune)
  (assert$ (not (x-xrunep rune))
           (list* :hyp rune n)))

(defabbrev hyp-xrune-rune (xrune)
  (assert$ (and (x-xrunep xrune)
                (eq (car xrune) :hyp))
           (cadr xrune)))

(defabbrev conc-xrune (rune)
  (assert$ (not (x-xrunep rune))
           (list* :conc rune)))

(defabbrev conc-xrune-rune (xrune)
  (assert$ (and (x-xrunep xrune)
                (eq (car xrune) :conc))
           (cdr xrune)))

(defabbrev xrune-rune (xrune)
  (cond ((x-xrunep xrune)
         (if (eq (car xrune) :hyp)
             (cadr xrune)
           (cdr xrune)))
        (t xrune)))

(defabbrev rune= (rune1 rune2)
  (and (eq (car rune1) (car rune2))
       (equal (cdr rune1) (cdr rune2))))

(defabbrev xrune= (xrune1 xrune2)
  (cond ((eq (car xrune1) :hyp)
         (and (eq (car xrune2) :hyp)
              (rune= (cadr xrune1) (cadr xrune2))
              (eql (cddr xrune1) (cddr xrune2))))
        ((eq (car xrune1) :conc)
         (and (eq (car xrune2) :conc)
              (rune= (cdr xrune1) (cdr xrune2))))
        (t (rune= xrune1 xrune2))))

(defun prettyify-xrune (xrune)

; We sort :hyp xrunes first by their rune (see sort-xrune-alist-by-rune), which
; is why a hyp xrune is of the form (:hyp rune . n) rather than (:hyp n
; . rune).  But the latter is more pleasant to view.

  (cond ((eq (car xrune) :hyp)
         (list* :hyp (cddr xrune) (cadr xrune)))
        (t xrune)))

(defrec accp-info

; The "s" and "f" suffixes below suggest "success" and "failure", though a
; better distinction is between "useful work" and "useless work".  Our
; user-level reports say "useful" and "useless".  See just below for a
; description of fields.

  (((cnt-s . cnt-f) . (stack-s . stack-f))
   xrune-stack
   xrunep
   totals
   .
   old-accp-info ; previous accp-info, supporting accumulated-persistence-oops
   )
  t)

; Cnt-s is the total number of lemmas tried that have led to a successful
; application.

; Cnt-f is similar but for lemmas whose application failed (typically because a
; hypothesis was not relieved).

; Stack-s (resp. stack-f) is a stack of old values of cnt-s (resp. cnt-f).

; Xrune-stack is a list of xrunes corresponding to stack-s and stack-f, where
; each xrune corresponds to a call of push-accp made on behalf of that xrune.

; Xrunep is true if we are to collect information for hypothesis and conclusion
; xrunes, and is nil otherwise.

; Totals is a stack of the accumulated totals, initially '(nil); it is one
; longer than the common length of stack-s and stack-f.  Each element of the
; stack is a list associating xrunes with totals accumulated for a
; corresponding xrune (i.e., an ancestral call of push-accp), as follows.

(defrec accp-entry

; Warning.  We construct lists of such entries that we refer to as alists.
; Before changing the shape of this record, consider whether we are relying on
; it being a record whose car is its :xrune field.  See for example
; sort-xrune-alist-by-rune1.

; The "s" and "f" suffixes below suggest "success" and "failure", though a
; better distinction is between "useful work" and "useless work".  Our
; user-level reports say "useful" and "useless".  See just below for a further
; description of the fields.

  (xrune . ((n-s . ap-s)
            .
            (n-f . ap-f)))
  t)

; Each element of stack-s (resp. stack-f) corresponds to an attempt to apply a
; certain xrune and the element is the value of cnt-s (resp. cnt-f) at the time
; the attempt started.  When the attempt is successful, we increase cnt-s,
; first by one if we have a rune rather than a hyp-xrune or conc-xrune, and
; then by the difference of the current value of cnt-s with the old value (on
; top of stack-s) to find out how many lemmas were usefully tried under that
; xrune, and we accumulate that difference into the success fields of the
; current totals for that xrune; similarly for cnt-f and useless tries.  When
; the attempt fails, all accumulation is into the failure (useless) fields of
; the totals.  The accumulated totals is a stack of lists, each of which
; contains elements associating xrunes with values n-s, ap-s, n-f, and ap-f,
; where n-s is the number of times xrune was pushed onto the stack and
; successfully applied, ap-s is the accumulated persistence of useful
; applications of that xrune (the total number of applications while that xrune
; was on the stack, not yet including such applications that are recorded in
; more recent stack frames), and n-f and ap-f are similar but for failed
; applications of that xrune.

; Performance: We have seen (Version_3.2.1) about a 50% increase in time with
; accumulated-persistence turned on, in very limited experiments.  In later
; versions we have found a significantly smaller increase unless enhanced
; statistics are gathered.  Here are results using code developed after
; Version_4.1, using Allegro CL.

; In (community) books directory workshops/2004/legato/support/
; (see below for discussion of which forms were submitted for each experiment):
;
; (set-inhibit-output-lst '(prove proof-tree))
; ;; (ld "/projects/acl2/devel-misc/patches/accumulated-persistence-hyps-rhs/patch.lisp")
; ;; (value :q)
; ;;; (load "/projects/acl2/devel-misc/patches/accumulated-persistence-hyps-rhs/patch.fasl")
; ;; (load "/projects/acl2/devel-misc/patches/accumulated-persistence-hyps-rhs/old.fasl")
; ;; (lp)
; ; (accumulated-persistence t)
; (time$ (ld "proof-by-generalization-mult.lisp"))
;
; No accp (skip commented forms)
; ; 97.01 seconds realtime, 95.54 seconds runtime.
;
; Old accp (include only one commented form, (accumulated-persistence t))
; ; 114.82 seconds realtime, 113.46 seconds runtime.
;
; New accp (include all commented forms except ;;;)
; ; 164.95 seconds realtime, 163.69 seconds runtime.
;
; New accp (include all commented forms)
; ; 165.09 seconds realtime, 163.90 seconds runtime.
;
; The results above were based on code that always gave results for a :conc
; xrune.  We now skip that xrune if there are no hypotheses, but that didn't
; make much difference:
; ; 164.84 seconds realtime, 163.50 seconds runtime.

(defun merge-accumulated-persistence-aux (xrune entry alist)
  (cond ((endp alist)

; See the comment below merge-accumulated-persistence for an attempt we made to
; avoid this unfortunate case (unfortunate because we consed up a new alist
; rather than just pushing the entry on the front).

         (list entry))
        ((xrune= xrune (access accp-entry (car alist) :xrune))
         (cons (make accp-entry
                     :xrune xrune
                     :n-s (+ (access accp-entry entry :n-s)
                             (access accp-entry (car alist) :n-s))
                     :ap-s (+ (access accp-entry entry :ap-s)
                              (access accp-entry (car alist) :ap-s))
                     :n-f (+ (access accp-entry entry :n-f)
                             (access accp-entry (car alist) :n-f))
                     :ap-f (+ (access accp-entry entry :ap-f)
                              (access accp-entry (car alist) :ap-f)))
               (cdr alist)))
        (t (cons (car alist)
                 (merge-accumulated-persistence-aux xrune entry (cdr alist))))))

(defun merge-accumulated-persistence-rec (new-alist old-alist)
  (cond ((endp new-alist) old-alist)
        (t (merge-accumulated-persistence-rec
            (cdr new-alist)
            (merge-accumulated-persistence-aux
             (access accp-entry (car new-alist) :xrune)
             (car new-alist)
             old-alist)))))

(defun merge-accumulated-persistence (new-alist old-alist)

; We tried an approach using sorting with rune-< (before we considered xrunes),
; but it was much more expensive.  We used as an example:
; cd books/workshops/2004/legato/support/
; acl2::(set-inhibit-output-lst '(prove proof-tree))
; (accumulated-persistence t)
; (time$ (ld "proof-by-generalization-mult.lisp"))

; All timings below are in GCL 2.6.7.

; Using rune-<:
;   real time       :    198.170 secs
;   run-gbc time    :    186.320 secs
;   child run time  :      0.000 secs
;   gbc time        :      7.720 secs

; Using the present approach, without sorting:

;   real time       :    141.170 secs
;   run-gbc time    :    129.070 secs
;   child run time  :      0.000 secs
;   gbc time        :      7.900 secs

; Approach through Version_3.2, without accounting for successes/failures:

;   real time       :    137.140 secs
;   run-gbc time    :    127.410 secs
;   child run time  :      0.000 secs
;   gbc time        :      5.930 secs

; See also below for alternate approach that didn't do as well.

  (cond ((null old-alist) ; optimization
         new-alist)
        (t (merge-accumulated-persistence-rec new-alist old-alist))))

; The following comment was written before the introduction of xrunes, and we
; have left it unchanged from that time.
;
; The following alternate code doesn't do as well, even though it uses nconc.
; The nconc version doesn't even seem much better on space (in fact worse in an
; Allegro CL test as reported by "space allocation": 669,110,675 cons cells in
; the nconc version vs. 593,299,188).  Compare the times below with those
; reported in merge-accumulated-persistence.
;
; Our basic idea was to avoid walking consing up a new alist in
; merge-accumulated-persistence-aux when the given rune wasn't already a key in
; the given alist.
;
; real time       :    157.780 secs
; run-gbc time    :    146.960 secs
; child run time  :      0.000 secs
; gbc time        :      8.990 secs
;
; Replacing nconc with revappend:
;
; real time       :    168.870 secs
; run-gbc time    :    149.930 secs
; child run time  :      0.000 secs
; gbc time        :      8.930 secs
;
; (defun merge-accumulated-persistence-1 (rune entry alist)
;   (cond ((endp alist)
;          (er hard 'merge-accumulated-persistence-1
;              "Implementation error: Unexpected end of list!  Please contact ~
;               the ACL2 implementors."))
;         ((rune= rune (access accp-entry (car alist) :rune))
;          (cons (make accp-entry
;                      :rune rune
;                      :n-s  (+ (access accp-entry entry :n-s)
;                               (access accp-entry (car alist) :n-s))
;                      :ap-s (+ (access accp-entry entry :ap-s)
;                               (access accp-entry (car alist) :ap-s))
;                      :n-f  (+ (access accp-entry entry :n-f)
;                               (access accp-entry (car alist) :n-f))
;                      :ap-f (+ (access accp-entry entry :ap-f)
;                               (access accp-entry (car alist) :ap-f)))
;                (cdr alist)))
;         (t (cons (car alist)
;                  (merge-accumulated-persistence-1 rune entry (cdr alist))))))
;
; (defun assoc-rune= (rune alist)
;   (cond ((endp alist) nil)
;         ((rune= rune (access accp-entry (car alist) :rune))
;          (car alist))
;         (t (assoc-rune= rune (cdr alist)))))
;
; (defun merge-accumulated-persistence-rec (new-alist old-alist new-alist-new)
;
; ; We merge into old-alist as we go along, except that entries in new-alist that
; ; are not in old-alist are put into new-alist-new.
;
;   (cond ((endp new-alist) (nconc new-alist-new old-alist))
;         (t (let* ((rune (access accp-entry (car new-alist) :rune))
;                   (pair (assoc-rune= rune old-alist)))
;              (merge-accumulated-persistence-rec
;               (cdr new-alist)
;               (cond (pair (merge-accumulated-persistence-1
;                            rune
;                            (car new-alist)
;                            old-alist))
;                     (t old-alist))
;               (cond (pair new-alist-new)
;                     (t (cons (car new-alist) new-alist-new))))))))
;
; ; Also would need to add final argument of nil to call of
; ; merge-accumulated-persistence-rec in merge-accumulated-persistence.
;

(defun add-accumulated-persistence-s (xrune delta alist original-alist acc)

; Warning: Keep this in sync with add-accumulated-persistence-f.

; See add-accumulated-persistence.

  (cond ((null alist)
         (cons (make accp-entry
                     :xrune xrune
                     :n-s  1
                     :ap-s (or delta 0)
                     :n-f  0
                     :ap-f 0)
               original-alist))
        ((xrune= xrune (access accp-entry (car alist) :xrune))
         (cons (cond (delta (change accp-entry (car alist)
                                    :ap-f 0 ; no change in :n-f
                                    :n-s  (1+ (access accp-entry (car alist)
                                                      :n-s))
                                    :ap-s (+ delta
                                             (access accp-entry (car alist)
                                                     :ap-s)
                                             (access accp-entry (car alist)
                                                     :ap-f))))
                     (t (assert$
                         (and (int= (access accp-entry (car alist) :ap-s)
                                    0)
                              (int= (access accp-entry (car alist) :ap-f)
                                    0))
                         (change accp-entry (car alist)
                                 :ap-f 0 ; no change in :n-f
                                 :n-s (1+ (access accp-entry (car alist)
                                                  :n-s))))))
               (revappend acc (cdr alist))))
        (t (add-accumulated-persistence-s
            xrune delta (cdr alist) original-alist
            (cons (car alist) acc)))))

(defun add-accumulated-persistence-f (xrune delta alist original-alist acc)

; Warning: Keep this in sync with add-accumulated-persistence-s.

; See add-accumulated-persistence.

; We assume that every :ap-s field of alist is 0, as is the case for alists
; produced by accumulated-persistence-make-failures.

  (cond ((null alist)
         (cons (make accp-entry
                     :xrune xrune
                     :n-s  0
                     :ap-s 0
                     :n-f  1
                     :ap-f (or delta 0))
               original-alist))
        ((xrune= xrune (access accp-entry (car alist) :xrune))
         (assert$
          (eql (access accp-entry (car alist) :ap-s)
               0)
          (cons (cond (delta (change accp-entry (car alist)
                                     :n-f  (1+ (access accp-entry (car alist)
                                                       :n-f))
                                     :ap-f (+ delta
                                              (access accp-entry (car alist)
                                                      :ap-f))))
                      (t (assert$
                          (eql (access accp-entry (car alist) :ap-f)
                               0)
                          (change accp-entry (car alist)
                                  :n-f (1+ (access accp-entry (car alist)
                                                   :n-f))))))
                (revappend acc (cdr alist)))))
        (t (add-accumulated-persistence-f
            xrune delta (cdr alist) original-alist
            (cons (car alist) acc)))))

(defun accumulated-persistence-make-failures (alist)
  (cond ((null alist) nil)
        (t
         (cons (change accp-entry (car alist)
                       :n-f (+ (access accp-entry (car alist) :n-f)
                               (access accp-entry (car alist) :n-s))
                       :n-s 0
                       :ap-f (+ (access accp-entry (car alist) :ap-f)
                                (access accp-entry (car alist) :ap-s))
                       :ap-s 0)
               (accumulated-persistence-make-failures (cdr alist))))))

(defun add-accumulated-persistence (xrune success-p delta alist-stack)

; This function is called by pop-accp-fn, to compute the new :totals field of
; the accp-info record.

; Alist-stack is a list of lists of accp-entry records (as in a :totals field
; of an accp-info record).  First, we modify the top of alist-stack to record
; everything as useless (failure) if success-p is nil.  Then, we merge that
; modification into the second element of alist-stack, after incrementing by 1
; for the given xrune's :n-s or :n-f and incrementing its :ap-s or :ap-f,
; according to success-p, by the given delta (which is the sum of the deltas
; for its :ap-s and :ap-f).  However, we make the following exception when
; delta is nil: then we do not increment :ap-s or :ap-f, which should be 0.

  (assert$
   (cdr alist-stack)
   (let* ((alist (if success-p
                     (car alist-stack)
                   (accumulated-persistence-make-failures (car alist-stack))))
          (new-alist (cond ((fake-rune-for-anonymous-enabled-rule-p
                             (xrune-rune xrune))
                            alist)
                           (success-p
                            (add-accumulated-persistence-s
                             xrune
                             delta
                             alist alist nil))
                           (t
                            (add-accumulated-persistence-f
                             xrune
                             delta
                             alist alist nil)))))
     (cons (merge-accumulated-persistence new-alist (cadr alist-stack))
           (cddr alist-stack)))))

(defmacro accumulated-persistence (flg)

; Warning: Keep this in sync with set-waterfall-parallelism-fn.

; Our convention is that if accumulated persistence is enabled, the data of the
; accumulated-persistence wormhole is non-nil.  If accumulated persistence is
; not enabled, the data is nil.

  (declare (xargs :guard (member-equal flg '(t 't nil 'nil :all ':all))))
  (let* ((flg (if (consp flg) (cadr flg) flg))
         (collect-hyp-and-conc-xrunes (eq flg :all)))
    `(cond
      #+acl2-par ; the following test is always false when #-acl2-par
      ((f-get-global 'waterfall-parallelism state)
       (er hard! 'accumulated-persistence
           "~x0 is not supported when waterfall-parallelism is enabled."
           'accumulated-persistence))
      (t (wormhole-eval
          'accumulated-persistence
          '(lambda (whs)
             (set-wormhole-data whs
                                (if ,flg
                                    (make accp-info
                                          :cnt-s 0
                                          :cnt-f 0
                                          :stack-s nil
                                          :stack-f nil
                                          :xrunep ,collect-hyp-and-conc-xrunes
                                          :totals '(nil)
                                          :old-accp-info
                                          (let ((info (wormhole-data whs)))
                                            (cond (info
; We avoid holding on to every past structure; one seems like enough.
                                                   (change accp-info info
                                                           :old-accp-info
                                                           nil))
                                                  (t nil))))
                                  nil)))
          nil)))))

(defmacro accumulated-persistence-oops ()
  (wormhole-eval
   'accumulated-persistence
   '(lambda (whs)
      (let* ((info (wormhole-data whs))
             (old (and info
                       (access accp-info info :old-accp-info))))
        (cond (old (set-wormhole-data whs old))
              (t (prog2$ (cw "No change: Unable to apply ~
                              accumulated-persistence-oops.~|")
                         whs)))))
   nil))

(defmacro set-accumulated-persistence (flg)
  `(accumulated-persistence ,flg))

(defun merge-car-> (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((> (car (car l1)) (car (car l2)))
         (cons (car l1) (merge-car-> (cdr l1) l2)))
        (t (cons (car l2) (merge-car-> l1 (cdr l2))))))

(defun merge-sort-car-> (l)
  (cond ((null (cdr l)) l)
        (t (merge-car-> (merge-sort-car-> (evens l))
                        (merge-sort-car-> (odds l))))))

(defconst *accp-major-separator*
  "   --------------------------------~%")

(defconst *accp-minor-separator*
  "      .............................~%")

(defun show-accumulated-persistence-phrase0 (entry key)

; Warning: Keep this in sync with show-accumulated-persistence-list.

  (let* ((xrune (access accp-entry entry :xrune))
         (n-s (access accp-entry entry :n-s))
         (n-f (access accp-entry entry :n-f))
         (n (+ n-s n-f))
         (ap-s (access accp-entry entry :ap-s))
         (ap-f (access accp-entry entry :ap-f))
         (ap (+ ap-s ap-f)))
    (let ((main-msg
           (msg "~c0 ~c1 (~c2.~f3~f4) ~y5"
                (cons ap 10)
                (cons n 8)
                (cons (floor ap n) 5)
                (mod (floor (* 10 ap) n) 10)
                (mod (floor (* 100 ap) n) 10)
                (prettyify-xrune xrune))))
      (case key
        ((:useless :ratio-a :frames-a :tries-a)
         (list main-msg))
        (otherwise
         (list main-msg
               (msg "~c0 ~c1    [useful]~%"
                    (cons ap-s 10)
                    (cons n-s 8))
               (msg "~c0 ~c1    [useless]~%"
                    (cons ap-f 10)
                    (cons n-f 8))))))))

(defun show-accumulated-persistence-phrase1 (key alist mergep acc)

; Alist has element of the form (x . accp-entry), where x is the key upon which
; we sorted.  Last-rune is true (initially t, generally a rune) if and only if
; we are calling show-accumulated-persistence with display = :merge.

  (cond ((null alist) acc)
        (t (show-accumulated-persistence-phrase1
            key
            (cdr alist)
            mergep
            (cons (cond ((and mergep
                              (cdr alist)
                              (equal (xrune-rune
                                      (access accp-entry
                                              (cdr (car (cdr alist)))
                                              :xrune))
                                     (xrune-rune
                                      (access accp-entry
                                              (cdr (car alist))
                                              :xrune))))

; The next entry to process for extending the accumulator has the same rune as
; the current entry in this case.

                         *accp-minor-separator*)
                        (t *accp-major-separator*))
                  (append (show-accumulated-persistence-phrase0
                           (cdr (car alist))
                           key)
                          acc))))))

(defun show-accumulated-persistence-remove-useless (alist acc)
  (cond ((null alist) (reverse acc))
        ((not (eql (access accp-entry (cdr (car alist))
                           :n-s)
                   0))
         (show-accumulated-persistence-remove-useless (cdr alist) acc))
        (t (show-accumulated-persistence-remove-useless
            (cdr alist)
            (cons (car alist) acc)))))

(defun show-accumulated-persistence-phrase-key (key entry lastcdr)
  (let* ((ap-s (access accp-entry entry :ap-s))
         (ap-f (access accp-entry entry :ap-f))
         (ap (+ ap-s ap-f))
         (n-s (access accp-entry entry :n-s))
         (n-f (access accp-entry entry :n-f))
         (n (+ n-s n-f)))
    (case key
      ((:frames :frames-a) (list* ap ap-s n n-s lastcdr))
      (:frames-s (list* ap-s ap n-s n lastcdr))
      (:frames-f (list* ap-f ap n-f n lastcdr))
      ((:tries :tries-a) (list* n n-s ap ap-s lastcdr))
      (:tries-s (list* n-s n ap-s ap lastcdr))
      (:tries-f  (list* n-f n ap-f ap lastcdr))
      (:useless (list* ap n lastcdr))
      (otherwise (list* (/ ap n) lastcdr)))))

(defun show-accumulated-persistence-phrase2-merge (key alist last-key-info)

; We augment the given alist by consing a sort key onto the front of each
; entry.  The sort key is based on both the entry and the given key, the
; first argument of show-accumulated-persistence.

  (cond ((null alist) nil)
        ((x-xrunep (access accp-entry (car alist) :xrune))
         (cons (cons (append last-key-info
                             (show-accumulated-persistence-phrase-key
                              key
                              (car alist)
                              nil))
                     (car alist))
               (show-accumulated-persistence-phrase2-merge
                key
                (cdr alist)
                last-key-info)))
        (t (let ((next-key-info
                  (show-accumulated-persistence-phrase-key
                   key
                   (car alist)
                   (list (access accp-entry (car alist) :xrune)))))
             (cons (cons (append next-key-info '(t))
                         (car alist))
                   (show-accumulated-persistence-phrase2-merge
                    key
                    (cdr alist)
                    next-key-info))))))

(defun show-accumulated-persistence-phrase2-not-merge (key alist)
  (cond ((null alist) nil)
        (t (cons (cons (show-accumulated-persistence-phrase-key key
                                                                (car alist)
                                                                nil)
                       (car alist))
                 (show-accumulated-persistence-phrase2-not-merge
                  key (cdr alist))))))

(defun show-accumulated-persistence-phrase2 (key alist mergep)
  (cond (mergep (show-accumulated-persistence-phrase2-merge key alist nil))
        (t (show-accumulated-persistence-phrase2-not-merge key alist))))

(defun split-xrune-alist (alist rune-alist hyp-xrune-alist conc-xrune-alist)

; See sort-rune-alist-for-xrunes.

  (cond ((endp alist)
         (mv rune-alist hyp-xrune-alist conc-xrune-alist))
        (t (let ((xrune (access accp-entry (car alist) :xrune)))
             (case (car xrune)
               (:hyp  (split-xrune-alist (cdr alist)
                                         rune-alist
                                         (cons (car alist) hyp-xrune-alist)
                                         conc-xrune-alist))
               (:conc (split-xrune-alist (cdr alist)
                                         rune-alist
                                         hyp-xrune-alist
                                         (cons (car alist) conc-xrune-alist)))
               (t     (split-xrune-alist (cdr alist)
                                         (cons (car alist) rune-alist)
                                         hyp-xrune-alist
                                         conc-xrune-alist)))))))

(defun sort-xrune-alist-by-rune1 (rune-alist hyp-xrune-alist conc-xrune-alist
                                             acc)

; Each input alist is a list of accp-entry records, sorted by lexorder --
; indeed sorted by the cars, which are distinct xrunes.  See
; sort-rune-alist-for-xrunes.  We return the (disjoint) union of the three
; inputs, such that every record for a :hyp or :conc xrune is preceded by an
; entry whose :xrune is either another such xrune or is the corresponding rune.

  (cond ((endp rune-alist)
         (assert$ (and (null hyp-xrune-alist)
                       (null conc-xrune-alist))
                  acc))
        ((and hyp-xrune-alist
              (equal (hyp-xrune-rune (caar hyp-xrune-alist))
                     (caar rune-alist)))
         (sort-xrune-alist-by-rune1 rune-alist
                                    (cdr hyp-xrune-alist)
                                    conc-xrune-alist
                                    (cons (car hyp-xrune-alist) acc)))
        ((and conc-xrune-alist
              (equal (conc-xrune-rune (caar conc-xrune-alist))
                     (caar rune-alist)))
         (sort-xrune-alist-by-rune1 rune-alist
                                    hyp-xrune-alist
                                    (cdr conc-xrune-alist)
                                    (cons (car conc-xrune-alist) acc)))
        (t
         (sort-xrune-alist-by-rune1 (cdr rune-alist)
                                    hyp-xrune-alist
                                    conc-xrune-alist
                                    (cons (car rune-alist) acc)))))

(defun sort-xrune-alist-by-rune (alist display)

; Alist is a list of accp-entry records.  We sort them such that every record
; for a :hyp or :conc xrune is preceded either by an entry whose :xrune is
; either another such xrune or is the corresponding rune.

  (cond ((not (member-eq display '(nil :merge)))
         alist)
        (t (mv-let (rune-alist hyp-xrune-alist conc-xrune-alist)
                   (split-xrune-alist alist nil nil nil)
                   (cond ((eq display nil) rune-alist)
                         (t ; (eq display :merge)
                          (sort-xrune-alist-by-rune1
                           (merge-sort-lexorder rune-alist)
                           (merge-sort-lexorder hyp-xrune-alist)
                           (merge-sort-lexorder conc-xrune-alist)
                           nil)))))))

(defun pop-accp-fn (info success-p)

; Warning: Keep the branches below in sync.  We considered merging them into a
; single branch, but the fields changed are different in each case, so we keep
; the cases separate in order to save a few conses.

; This function returns an updated version of the given accp-info record when
; exiting the accumulated-persistence wormhole.  Most of the update is done
; directly in the code below, but add-accumulated-persistence is called to
; update the :totals field, which is a stack of alists that record the
; accumulations.

; If xrune is a member of (cdr xrune-stack), then we avoid accumulating values
; for xrune here.  We will ultimately do such accumulation for the top-level
; occurrence of xrune in xrune-stack.  See the Essay on Accumulated
; Persistence.

  (let* ((xrune-stack (access accp-info info :xrune-stack))
         (xrune (car xrune-stack))
         (xp (x-xrunep xrune))
         (new-cnt
          (and (not xp) ; else new-cnt is irrelevant
               (cond (success-p
                      (if (fake-rune-for-anonymous-enabled-rule-p xrune)
                          (access accp-info info :cnt-s)
                        (1+ (access accp-info info :cnt-s))))
                     (t
                      (if (fake-rune-for-anonymous-enabled-rule-p xrune)
                          (access accp-info info :cnt-f)
                        (1+ (access accp-info info :cnt-f)))))))
         (top-level-p (not (member-equal xrune (cdr xrune-stack)))))
    (cond
     (xp
      (change accp-info info
              :stack-s (cdr (access accp-info info :stack-s))
              :stack-f (cdr (access accp-info info :stack-f))
              :xrune-stack (cdr xrune-stack)
              :totals (add-accumulated-persistence
                       xrune
                       success-p
                       (and top-level-p
                            (+ (- (access accp-info info :cnt-s)
                                  (car (access accp-info info :stack-s)))
                               (- (access accp-info info :cnt-f)
                                  (car (access accp-info info :stack-f)))))
                       (access accp-info info :totals))))
     (success-p
      (change accp-info info
              :cnt-s new-cnt
              :stack-s (cdr (access accp-info info :stack-s))
              :stack-f (cdr (access accp-info info :stack-f))
              :xrune-stack (cdr xrune-stack)
              :totals (add-accumulated-persistence
                       xrune
                       success-p
                       (and top-level-p
                            (+ (- new-cnt
                                  (car (access accp-info info :stack-s)))
                               (- (access accp-info info :cnt-f)
                                  (car (access accp-info info :stack-f)))))
                       (access accp-info info :totals))))
     (t
      (change accp-info info
              :cnt-f new-cnt
              :stack-s (cdr (access accp-info info :stack-s))
              :stack-f (cdr (access accp-info info :stack-f))
              :xrune-stack (cdr xrune-stack)
              :totals (add-accumulated-persistence
                       xrune
                       success-p
                       (and top-level-p
                            (+ (- (access accp-info info :cnt-s)
                                  (car (access accp-info info :stack-s)))
                               (- new-cnt
                                  (car (access accp-info info :stack-f)))))
                       (access accp-info info :totals)))))))

(defun pop-accp-fn-iterate (info n)
  (if (zp n)
      info
    (pop-accp-fn-iterate (pop-accp-fn info

; For this call of pop-accp-fn, the value of success-p is not terribly
; important at the time we are writing this code, since it is used only in
; show-accumulated-persistence-phrase, only when we throw out information that
; distinguishes between useful and useless.  We choose t here in case we ever
; use such information, because we do not want to under-report successes, as
; that could encourage the disabling of rules that are useful even though they
; have been reported as useless.

                                      t)
                         (1- n))))

(defun show-accumulated-persistence-list (alist acc)

; Alist has element of the form (x . accp-entry), where x is the key upon which
; we sorted.

; Warning: Keep this in sync with show-accumulated-persistence-phrase0 (but
; note that the recursion is based on that of
; show-accumulated-persistence-phrase1).

  (cond ((endp alist) acc)
        (t
         (let* ((entry (cdar alist))
                (xrune (access accp-entry entry :xrune))
                (n-s (access accp-entry entry :n-s))
                (n-f (access accp-entry entry :n-f))
                (n (+ n-s n-f))
                (ap-s (access accp-entry entry :ap-s))
                (ap-f (access accp-entry entry :ap-f))
                (ap (+ ap-s ap-f)))
           (show-accumulated-persistence-list
            (cdr alist)
            (cons (list ap n (prettyify-xrune xrune))
                  acc))))))

(defun show-accumulated-persistence-phrase (key/display accp-info)

; Alist is the accumulated totals alist from the wormhole data field of
; wormhole-status of the 'accumulated-persistence wormhole.  Each element is of
; the form (xrune n . ap) and we sort them into descending order on the
; specified key.  Key should be one of the sortkey values from the guard of
; show-accumulated-persistence.

  (let* ((key (car key/display))
         (display (cdr key/display))
         (xrune-stack (access accp-info accp-info :xrune-stack))
         (accp-info (cond ((and xrune-stack
                                (member-eq key '(:frames-a :tries-a)))
                           (pop-accp-fn-iterate accp-info (length xrune-stack)))
                          (t accp-info)))
         (totals (access accp-info accp-info :totals)))
    (cond
     ((null totals)
      (msg "There is no accumulated persistence to show.  Evaluate ~x0 to ~
            activate gathering of accumulated-persistence statistics.~|"
           '(accumulated-persistence t)))
     ((eq key :runes)
      (msg "~x0"
           (merge-sort-lexorder (strip-cars (car (last totals))))))
     (t (let* ((mergep (eq display :merge))
               (alist (merge-sort-lexorder
                       (show-accumulated-persistence-phrase2
                        key
                        (sort-xrune-alist-by-rune (car (last totals))
                                                  display)
                        mergep)))
               (alist (if (eq key :useless)
                          (show-accumulated-persistence-remove-useless alist
                                                                       nil)
                        alist))
               (header-for-results
                (if (eq display :list)
                    "List of entries (:frames :tries rune):~|"
                  "   :frames   :tries    :ratio  rune"))
               (msg-for-results
                (if (eq display :list)
                    (msg "~|~x0~|"
                         (show-accumulated-persistence-list alist nil))
                  (msg "~*0~@1"
                       (list "" "~@*" "~@*" "~@*"
                             (show-accumulated-persistence-phrase1
                              key
                              alist
                              mergep
                              nil))
                       *accp-major-separator*))))
          (cond ((null (cdr totals))
                 (msg "Accumulated Persistence~@0~|~%~@1~%~@2"
                      (if xrune-stack
                          "" ; we merged, so don't know just what was useful
                        (msg " (~x0 :tries useful, ~x1 :tries not useful)"
                             (access accp-info accp-info :cnt-s)
                             (access accp-info accp-info :cnt-f)))
                      header-for-results
                      msg-for-results))
                (t
                 (msg "Accumulated Persistence~|~%~
                       ***************************************~|~
                       *** NOTE: INCOMPLETE!!!~|~
                       *** ~x0 rule attempts are not considered below.~|~
                       *** Use :frames-a or :tries-a to get more complete ~
                           totals.~|~
                       ***************************************~|~
                       ~%~@1~%~@2"
                      (- (+ (access accp-info accp-info
                                    :cnt-s)
                            (access accp-info accp-info
                                    :cnt-f)
                            (length xrune-stack))
                         (+ (car (last (access accp-info accp-info
                                               :stack-s)))
                            (car (last (access accp-info accp-info
                                               :stack-f)))))
                      header-for-results
                      msg-for-results))))))))

(defmacro show-accumulated-persistence (&optional (sortkey ':frames)
                                                  (display 't))
  (declare (xargs :guard
                  (and (member-eq sortkey
                                  '(:ratio
                                    :frames :frames-s :frames-f :frames-a
                                    :tries :tries-s :tries-f :tries-a
                                    :useless
                                    :runes))
                       (member-eq display
                                  '(t nil :raw :merge :list)))))

; This function engages is in a little song-and-dance about the entry code for
; the accumulated-persistence wormhole.  If the user has requested that we
; print the accumulated-persistence data, we enter the wormhole to do it --
; even accumulated persistence has not been turned on.  So we have to set the
; code to :ENTER.  But we have to remember to turn it back off upon leaving the
; wormhole.  How to we know, once we're in the wormhole, whether to set the
; code to :SKIP or :ENTER?  When we switch :SKIP to :ENTER to go inside we set
; the data field to :RETURN-TO-SKIP.  This doesn't hurt anything because if the
; code was :SKIP, the data was nil anyway.  Once inside, if the data is
; :RETURN-TO-SKIP we set the entry code back to :SKIP.

  `(wormhole 'accumulated-persistence
             '(lambda (whs)
                (set-wormhole-entry-code whs :ENTER))
             ',(cons sortkey display)
             '(state-global-let*
               ((print-base 10 set-print-base)
                (print-radix nil set-print-radix))
               (pprogn
                (io? temporary nil state
                     nil
                     (fms "~@0"
                          (list (cons #\0
                                      (show-accumulated-persistence-phrase
                                       (f-get-global 'wormhole-input state)
                                       (wormhole-data
                                        (f-get-global 'wormhole-status state)))))
                          *standard-co*
                          state nil))
                (value :q)))
             :ld-prompt  nil
             :ld-missing-input-ok nil
             :ld-pre-eval-filter :all
             :ld-pre-eval-print nil
             :ld-post-eval-print :command-conventions
             :ld-evisc-tuple nil
             :ld-error-triples  t
             :ld-error-action :error
             :ld-query-control-alist nil
             :ld-verbose nil))

(defun push-accp-fn (rune x-info info)
  (let ((xrune (cond ((natp x-info)
                      (hyp-xrune x-info rune))
                     ((eq x-info :conc)
                      (conc-xrune rune))
                     ((null x-info)
                      rune)
                     (t (er hard 'push-accp
                            "Implementation error: Bad value of x-info, ~x0."
                            x-info)))))
    (change accp-info info
            :xrune-stack (cons xrune (access accp-info info :xrune-stack))
            :stack-s (cons (access accp-info info :cnt-s)
                           (access accp-info info :stack-s))
            :stack-f (cons (access accp-info info :cnt-f)
                           (access accp-info info :stack-f))
            :totals (cons nil
                          (access accp-info info :totals)))))

(defun push-accp (rune x-info)
  (wormhole-eval 'accumulated-persistence
                 '(lambda (whs)

; The wormhole status of the accumulated-persistence wormhole is of the form
; (:key . info), where :key is either :ENTER or :SKIP and info is an accp-info
; record or NIL.  When this code is eventually converted to :logic mode and we
; wish to verify its guards we are going to have to confront the question of
; maintaining invariants on a wormhole's status so we don't have to check
; guards at runtime.  For example, in the code below, (cdr whs) is assumed to
; be a accp-info record.  See the Essay on Wormholes.

                    (let ((info (wormhole-data whs)))
                      (cond ((null info) whs)
                            ((or (null x-info)
                                 (access accp-info info :xrunep))
                             (set-wormhole-data
                              whs
                              (push-accp-fn rune x-info info)))
                            (t whs))))

; We avoid locking push-accp, in order to benefit the performance of ACL2(p).
; Note that accumulated persistence is disallowed when waterfall-parallelism is
; enabled; see accumulated-persistence and set-waterfall-parallelism-fn.

                 (cons :no-wormhole-lock rune)))

(defun pop-accp (success-p x-info)
  (wormhole-eval 'accumulated-persistence
                 '(lambda (whs)
                    (let ((info (wormhole-data whs)))
                      (cond ((null info) whs)
                            ((or (null x-info)
                                 (access accp-info info :xrunep))
                             (set-wormhole-data whs
                                                (pop-accp-fn info success-p)))
                            (t whs))))

; We avoid locking pop-accp, in order to benefit the performance of ACL2(p).
; Note that accumulated persistence is disallowed when waterfall-parallelism is
; enabled; see accumulated-persistence and set-waterfall-parallelism-fn.

                 (cons :no-wormhole-lock success-p)))

(defmacro with-accumulated-persistence (rune vars success-p body
                                             &optional
                                             x-info
                                             (condition 'nil condition-p))

; X-info can be :conc to indicate that we are tracking the right-hand side of a
; rule, or a positive integer n to indicate that we are tracking the nth
; hypothesis of a rule.  Otherwise x-info should be nil.

; Vars is a list of variable names, except that the first member of vars may be
; of the form (the type var), which is treated the same as var except that a
; suitable type declaration is added (which can assist GCL in avoiding boxing
; of fixnums).

  (flet ((fix-var (var)
                  (if (consp var) ; (the type var)
                      (caddr var)
                    var))
         (fix-var-declares (var)
                           (and (consp var) ; (the type var)
                                `((declare (type ,(cadr var) ,(caddr var)))))))
    (flet ((fix-vars (vars)
                     (if (consp vars)
                         (cons (fix-var (car vars))
                               (cdr vars))
                       vars)))
      (let ((form
             `(prog2$
               (push-accp ,rune ,x-info)
               ,(cond ((and (true-listp vars)
                            (= (length vars) 1))
                       `(let ((,(fix-var (car vars))
                               ,body))
                          ,@(fix-var-declares (car vars))
                          (prog2$
                           (pop-accp ,success-p ,x-info)
                           ,(fix-var (car vars)))))
                      (t `(mv-let ,(fix-vars vars)
                                  ,body
                                  ,@(fix-var-declares (car vars))
                                  (prog2$
                                   (pop-accp ,success-p ,x-info)
                                   (mv ,@(fix-vars vars)))))))))
        (cond (condition-p
               `(cond (,condition ,form)
                      (t ,body)))
              (t form))))))

;; Historical Comment from Ruben Gamboa:
;; Changed the assumptions based on rational to realp.

(defun assume-true-false-< (not-flg arg1 arg2 ts1 ts2 type-alist ttree xttree
                                    w)

; This function returns an extended type-alist by assuming (< ts1 ts2) true if
; not-flg is nil, but assuming (< ts1 ts2) false if not-flg is not nil.  It
; assumes that type-set (and hence type-set-<) was not able to decide the truth
; or falsity of (< ts1 ts2).  We could put this code in-line in
; assume-true-false, but the `true-type-alist' and `false-type-alist' are dealt
; with symmetrically, so it's convenient to share code via this function.

; Here are the cases we handle.  In this sketch we are glib about the
; possibility that arg1 or arg2 is nonnumeric or complex, but our code handles
; the more general situation.

; When we assume (< arg1 arg2) true,
; * if arg1 is positive then arg2 is positive
; * if arg1 is in the nonnegatives then arg2 is strictly positive
; * if arg2 is in the nonpositives then arg1 is strictly negative
; When we say "arg1 is in the nonnegatives" we mean to include the case where
; arg1 is strictly positive.  Note also that if arg1 may be negative, then arg2
; could be anything (given that we've made the normalization in
; assume-true-false-rec before calling this function).  Thus, the above two
; cases are as strong as we can be.

; When we assume (< arg1 arg2) false we find it easier to think about assuming
; (<= arg2 arg1) true:
; * if arg1 is negative, then arg2 is negative
; * if arg1 is nonpositive, then arg2 is nonpositive
; * if arg2 is nonnegative, then arg1 is nonnegative
; Note that if arg1 may be positive then arg2 could be anything, so there are
; no other cases we can express.

  (cond
   ((not not-flg) ; Assume that (< ts1 ts2) is true.
    (let ((strongp (and (or (ts-subsetp ts1 *ts-positive-integer*)
                            (and (quotep arg1)
                                 (rationalp (unquote arg1))
                                 (<= 1 (unquote arg1))))
                        (ts-intersectp ts2 *ts-one*))))
      (cond
; assuming true: if arg1 is at least 1 then arg2 is positive and not 1
       (strongp

; The test implies that we are dealing with (< arg1 arg2) where arg1 is a
; positive integer.  We are thus allowed to deduce that arg2 is positive or
; complex, but not 1.  That is, we may delete the non-positive reals,
; non-numbers, and 1 from its existing type-set.  We know that *ts-one* is
; included in ts2 (by the second condition of strongp), so the intersection
; below is strictly smaller than ts2.  (The next case handles similar cases
; without involving 1.)

; This case allows us, for example, to prove (thm (implies (< 5/2 x) (equal
; (foo (bitp x)) (foo nil)))) where we have introduced (defstub foo (x) t).

; A worry is that the intersection below replaces ts2 by *ts-empty*.  Can that
; happen?  If it did, then we would have that arg1 is a positive integer, and
; arg2 is a non-positive real or a non-number or 1.  Supposedly type-set-<
; would have then reported that (< arg1 arg2) must be false and mbf would be t.
; So the empty intersection cannot arise.

        (extend-type-alist
         ;;*** -simple
         arg2
         (ts-intersection ts2
                          (ts-complement *ts-one*)
                          #+:non-standard-analysis
                          (ts-union *ts-positive-real*
                                    *ts-complex*)
                          #-:non-standard-analysis
                          (ts-union *ts-positive-rational*
                                    *ts-complex-rational*))
         (cons-tag-trees ttree xttree)
         type-alist w))
; assuming true: if arg1 is nonnegative then arg2 is positive
       ((and (ts-subsetp ts1
                         (ts-union #+:non-standard-analysis
                                   *ts-non-negative-real*
                                   #-:non-standard-analysis
                                   *ts-non-negative-rational*
                                   (ts-complement *ts-acl2-number*)))
             (ts-intersectp
              ts2
              (ts-complement
               #+:non-standard-analysis
               (ts-union *ts-positive-real* *ts-complex*)
               #-:non-standard-analysis
               (ts-union *ts-positive-rational* *ts-complex-rational*))))

; The test says: We are dealing with (< arg1 arg2) where arg1 is non-negative
; or a non-number.  We are thus allowed to deduce that arg2 is strictly
; positive or complex.  That is, we may delete the non-positive reals and
; non-numbers from its existing type-set.  If that doesn't change anything, we
; don't want to do it, so we have the conjunct immediately above that says arg2
; contains some non-positive reals or some non-numbers.

; A worry is that the intersection below is empty.  Can that happen?  If it
; did, then we would have that arg1 is a non-negative real or a non-number, and
; arg2 is a non-positive real or a non-number.  Supposedly type-set-< would
; have then reported that (< arg1 arg2) must be false and mbf would be t.  So
; the empty intersection cannot arise.

        (extend-type-alist
         ;;*** -simple
         arg2
         (ts-intersection ts2
                          #+:non-standard-analysis
                          (ts-union *ts-positive-real* *ts-complex*)
                          #-:non-standard-analysis
                          (ts-union *ts-positive-rational*
                                    *ts-complex-rational*))
         (cons-tag-trees ttree xttree)
         type-alist w))
; assuming true: if arg2 is not positive then arg1 is negative
       ((and (ts-subsetp ts2
                         (ts-union #+:non-standard-analysis
                                   *ts-non-positive-real*
                                   #-:non-standard-analysis
                                   *ts-non-positive-rational*
                                   (ts-complement *ts-acl2-number*)))
             (ts-intersectp
              ts1
              (ts-complement
               #+:non-standard-analysis
               (ts-union *ts-negative-real* *ts-complex*)
               #-:non-standard-analysis
               (ts-union *ts-negative-rational* *ts-complex-rational*))))
        (extend-type-alist
         ;;*** -simple
         arg1
         (ts-intersection ts1
                          #+:non-standard-analysis
                          (ts-union *ts-negative-real* *ts-complex*)
                          #-:non-standard-analysis
                          (ts-union *ts-negative-rational*
                                    *ts-complex-rational*))
         (cons-tag-trees ttree xttree)
         type-alist w))
       (t type-alist))))

; The remaining cases assume that (< ts1 ts2) is false.

; assuming false: if arg1 is negative then arg2 is negative
   ((and (ts-subsetp ts1
                     #+:non-standard-analysis
                     *ts-negative-real*
                     #-:non-standard-analysis
                     *ts-negative-rational*)
         (ts-intersectp ts2
                        #+:non-standard-analysis
                        (ts-complement (ts-union *ts-complex*
                                                 *ts-negative-real*))
                        #-:non-standard-analysis
                        (ts-complement (ts-union *ts-complex-rational*
                                                 *ts-negative-rational*))))
; We are dealing with (not (< arg1 arg2)) which is (<= arg2 arg1) and we here
; know that arg1 is negative.  Thus, arg2 must be negative or complex.  See the
; case below for more details.

    (extend-type-alist
     ;;*** -simple
     arg2
     (ts-intersection ts2
                      #+:non-standard-analysis
                      (ts-union *ts-complex*
                                *ts-negative-real*)
                      #-:non-standard-analysis
                      (ts-union *ts-complex-rational*
                                *ts-negative-rational*))
     (cons-tag-trees ttree xttree)
     type-alist w))
; assuming false: if arg1 is not positive then arg2 is not positive
   ((and (ts-subsetp ts1
                     (ts-union #+:non-standard-analysis
                               *ts-non-positive-real*
                               #-:non-standard-analysis
                               *ts-non-positive-rational*
                               (ts-complement *ts-acl2-number*)))
         (ts-intersectp ts2
                        #+:non-standard-analysis
                        *ts-positive-real*
                        #-:non-standard-analysis
                        *ts-positive-rational*))

; Here we are dealing with (not (< arg1 arg2)) which is (<= arg2 arg1).  We
; know arg1 is <= 0.  We will thus deduce that arg2 is <= 0, and hence not a
; positive real, if we don't already know it.  But the worry again arises
; that the intersection of arg2's known type and the complement of the
; positive-reals is empty.  Suppose it were.  Then arg2 is a strictly
; positive real.  But if arg1 is a non-positive real or a non-number
; and arg2 is a positive real, then type-set-< knows that (< arg1 arg2) is
; true.  Thus, this worry is again baseless.

    (extend-type-alist
     ;;*** -simple
     arg2
     (ts-intersection
      ts2
      (ts-complement #+:non-standard-analysis *ts-positive-real*
                     #-:non-standard-analysis *ts-positive-rational*))
     (cons-tag-trees ttree xttree)
     type-alist w))
; assuming false: if arg2 is positive then arg1 is positive
   ((and (ts-subsetp ts2
                     #+:non-standard-analysis *ts-positive-real*
                     #-:non-standard-analysis *ts-positive-rational*)
         (ts-intersectp ts1
                        (ts-complement
                         #+:non-standard-analysis
                         (ts-union *ts-complex* *ts-positive-real*)
                         #-:non-standard-analysis
                         (ts-union *ts-complex-rational*
                                   *ts-positive-rational*))))
    (extend-type-alist
     ;;*** -simple
     arg1
     (ts-intersection
      ts1
      #+:non-standard-analysis
      (ts-union *ts-complex* *ts-positive-real*)
      #-:non-standard-analysis
      (ts-union *ts-complex-rational*
                *ts-positive-rational*))
     (cons-tag-trees ttree xttree)
     type-alist w))
; assuming false: if arg2 is nonnegative then arg1 is nonnegative
   ((and (ts-subsetp
          ts2
          (ts-complement
           #+:non-standard-analysis
           (ts-union *ts-complex* *ts-negative-real*)
           #-:non-standard-analysis
           (ts-union *ts-complex-rational*
                     *ts-negative-rational*)))
         (ts-intersectp ts1
                        #+:non-standard-analysis *ts-negative-real*
                        #-:non-standard-analysis *ts-negative-rational*))
    (extend-type-alist
     ;;*** -simple
     arg1
     (ts-intersection
      ts1
      (ts-complement #+:non-standard-analysis *ts-negative-real*
                     #-:non-standard-analysis *ts-negative-rational*))
     (cons-tag-trees ttree xttree)
     type-alist w))
   (t type-alist)))

(defun mv-atf-2 (not-flg true-type-alist false-type-alist
                         new-term xnot-flg x shared-ttree xttree ignore)

; This function is a variation of mv-atf in which mbt, mbf, ttree1,
; and ttree2 are all known to be nil.  The scenario is that there is
; an implicit term that we want to assume true or false, and we have
; generated two other terms x and new-term to assume true or false
; instead, each with its own parity (xnot-flg and not-flg,
; respectively).  We want to avoid putting redundant information on
; the type-alist, which would happen if we are not careful in the case
; that x and new-term are the same term modulo their respective
; parities.

; The tag-tree shared-ttree justifies truth or falsity of new-term
; while xttree justifies truth or falsity of x.

; We assume that new-term is not a call of NOT.

; Ignore is :tta or :fta if we do not care about the value of true-type-alist
; or false-type-alist that is passed in (and may get passed out in the opposite
; position, due to not-flg).

  (let ((tta0 (and (not (eq ignore :tta))
                   (extend-type-alist-simple
                    new-term
                    *ts-t*
                    shared-ttree
                    true-type-alist)))
        (fta0 (and (not (eq ignore :fta))
                   (extend-type-alist-simple
                    new-term
                    *ts-nil*
                    shared-ttree
                    false-type-alist)))
        (same-parity (eq not-flg xnot-flg)))
    (cond
     ((equal new-term ; new-term is not a call of NOT, so we negate x
             (cond (same-parity x)
                   (t (dumb-negate-lit x))))
      (mv-atf not-flg nil nil tta0 fta0 nil nil))
     (t
      (let ((tta1 (extend-type-alist-simple
                   x
                   (if same-parity *ts-t* *ts-nil*)
                   xttree
                   tta0))
            (fta1 (extend-type-alist-simple
                   x
                   (if same-parity *ts-nil* *ts-t*)
                   xttree
                   fta0)))
        (mv-atf not-flg nil nil tta1 fta1 nil nil))))))

(defun binding-hyp-p (hyp alist wrld)

; Returns (mv forcep flg), where forcep is true if we have a call of force or
; case-split, in which case we consider the argument of that call for flg.  Flg
; indicates whether we have a call (equiv var term), where var is a free
; variable with respect to alist (typically a unifying substitution, but we
; only look at the cars) that we want to bind.  Starting with Version_2.9.4, we
; allow equiv to be an equivalence relation other than equal; however, to
; preserve existing proofs (in other words, to continue to allow kinds of
; equivalential reasoning done in the past), we only allow binding in the
; non-equal case when the right-hand side is a call of double-rewrite, which
; may well be what is desired anyhow.

; Starting with Version_2.7, we try all bindings of free variables.  Moreover,
; in the case that there are free variables, we formerly first looked in the
; type-alist before considering the special case of (equal v term) where v is
; free and term has no free variables.  Starting with Version_2.7 we avoid
; considerations of free variables when this special case arises, by handling
; it first.

  (let* ((forcep (and (nvariablep hyp)
                      (not (fquotep hyp))
                      (or (eq (ffn-symb hyp) 'force)
                          (eq (ffn-symb hyp) 'case-split))))
         (hyp (if forcep (fargn hyp 1) hyp))
         (eqp (equalityp hyp)))
    (mv forcep
        (cond (eqp (and (variablep (fargn hyp 1))
                        (not (assoc-eq (fargn hyp 1) alist))
                        (not (free-varsp (fargn hyp 2) alist))))
              (t

; We want to minimize the cost of the checks below.  In particular, we do the
; variablep check before the more expensive equivalence-relationp check (which
; can call getprop).

               (and (nvariablep hyp)
                    (not (fquotep hyp))
                    (fargs hyp)
                    (variablep (fargn hyp 1))
                    (equivalence-relationp (ffn-symb hyp) wrld)
                    (let ((arg2 (fargn hyp 2)))
                      (and (not (assoc-eq (fargn hyp 1) alist))
                           (ffn-symb-p arg2 'double-rewrite)
                           (not (free-varsp arg2 alist))))))))))

(defmacro adjust-ignore-for-atf (not-flg ignore)

; Here, we rebind ignore to indicate which type-alist (tta or fta) is
; irrelevant for passing into a function that will swap them if and only if
; not-flg is true.

  `(cond ((and ,not-flg (eq ,ignore :fta)) :tta)
         ((and ,not-flg (eq ,ignore :tta)) :fta)
         (t ,ignore)))

; To decide if backchaining has gone on long enough we use:

(defun backchain-limit-reachedp1 (n ancestors)
  (cond ((int= n 0) t)
        ((null ancestors) nil)
        (t (backchain-limit-reachedp1 (1- n) (cdr ancestors)))))

(defun backchain-limit-reachedp (n ancestors)

; Here n is the backchain-limit currently in effect; n must be either nil
; or a nonnegative integer, the former case being treated as infinity.
; Ancestors is the ancestors argument to relieve-hyp.  Its length is
; the number of times we have backchained already.  We decide whether
; the backchain limit has been reached (or exceeded).  This function
; is thus equivalent to (<= n (length ancestors)) for integers n.

  (and n (backchain-limit-reachedp1 n ancestors)))

(defun new-backchain-limit (new-offset old-limit ancestors)

; We are getting ready to relieve one of the hypotheses of a rule.
; New-offset is the backchain-limit associated with that hypothesis,
; old-limit is the current backchain-limit, and the length of
; ancestors is how many times we have already backchained.

  (cond ((null new-offset)

; Since the hypothesis allows unlimited backchaining, we impose no
; new limits.

         old-limit)
        ((null old-limit)

; Since we had been allowing unlimited backchaining, any new
; restrictions come from new-offset (which is known to be a
; non-negative integer).  Consider an example:
; ancestors is a list of length 3, and new-offset is 2.
; Here, we have backchained three times and wish to limit it
; to two more times, so we return 3 + 2 = 5.

         (+ (length ancestors) new-offset))
        (t
         (min (+ (length ancestors) new-offset)
              old-limit))))

(defproxy oncep-tp (* *) => *)

(defun oncep-tp-builtin (rune wrld)
  (declare (ignore rune wrld)
           (xargs :mode :logic :guard t))
  nil)

(defattach (oncep-tp oncep-tp-builtin)
  :skip-checks t)

(defun strengthen-recog-call (x)

; X is a recognizer call (r u).  This function normally returns (mv nil (fargn
; x 1)).  However, it may return (mv ts y) if (r u) implies the disjunction (or
; (ts' y) (r y), where (ts' y) is the assertion that y has type ts, and (not (r
; u)) implies (not (r y)).  For example, (integerp (+ '3 y)) is equivalent to
; (or (not (acl2-numberp y)) (integerp y)), so we return (mv (ts-complement
; *ts-acl2-number*) y) in that case.  Thus, the first argument serves both as a
; flag to indicate that something special is returned, and as a type-set that
; the caller is responsible for taking into account.

  (let ((arg (fargn x 1)))
    (case (ffn-symb x)
      (integerp
       (cond
        ((ffn-symb-p arg 'binary-+) ; (+ const term)
         (cond
          ((and (quotep (fargn arg 1))
                (integerp (unquote (fargn arg 1))))
           (mv (ts-complement *ts-acl2-number*)
               (fargn arg 2)))
          (t (mv nil arg))))
        (t (mv nil arg))))
      (rationalp
       (cond
        ((ffn-symb-p arg 'binary-+) ; (+ const term)
         (cond
          ((and (quotep (fargn arg 1))
                (rationalp (unquote (fargn arg 1))))
           (mv (ts-complement *ts-acl2-number*)
               (fargn arg 2)))
          (t (mv nil arg))))
        ((ffn-symb-p arg 'binary-*) ; (* const term)
         (cond
          ((and (quotep (fargn arg 1))
                (rationalp (unquote (fargn arg 1)))
                (not (eql 0 (unquote (fargn arg 1)))))
           (mv (ts-complement *ts-acl2-number*)
               (fargn arg 2)))
          (t (mv nil arg))))
        (t (mv nil arg))))
      (otherwise (mv nil arg)))))

(defun push-lemma? (rune ttree)
  (if rune
      (push-lemma rune ttree)
    ttree))

(defun strong-recognizer-expr-p (var x ens w)

; At the top level var is nil and x is a call of IF (which is why we test for
; such a call first, though it's a bit sad to have to do that duplicate test at
; the top level at all).

; We return (mv var tbr-true-ts tbr-false-ts tbr-runes), where var is nil on
; failure and otherwise var is the term being recognized everywhere through the
; IF structure of x -- unless var is :empty, signifying that we have only
; encountered the "trivial recognizer calls" *t* and *nil*.

; We don't use strengthen-recog-call here, in part because different
; recognizers in x could then give rise to different variables that are to be
; typed.

  (cond
   ((ffn-symb-p x 'if) ; see comment above
    (mv-let (var test-true-ts test-false-ts test-runes)
      (strong-recognizer-expr-p var (fargn x 1) ens w)
      (cond
       (var
        (mv-let (var tbr-true-ts tbr-false-ts tbr-runes)
          (strong-recognizer-expr-p (and (not (eq var :empty)) var)
                                    (fargn x 2) ens w)
          (cond
           (var
            (mv-let (var fbr-true-ts fbr-false-ts fbr-runes)
              (strong-recognizer-expr-p (and (not (eq var :empty)) var)
                                        (fargn x 3) ens w)
              (cond
               (var
                (mv var
                    (ts-union (ts-intersection test-true-ts
                                               tbr-true-ts)
                              (ts-intersection test-false-ts
                                               fbr-true-ts))
                    (ts-union (ts-intersection test-true-ts
                                               tbr-false-ts)
                              (ts-intersection test-false-ts
                                               fbr-false-ts))
                    (union-equal test-runes
                                 (union-equal tbr-runes
                                              fbr-runes))))
               (t (mv nil nil nil nil)))))
           (t (mv nil nil nil nil)))))
       (t (mv nil nil nil nil)))))
   ((variablep x)
    (mv nil nil nil nil))
   ((equal x *t*)
    (mv (or var :empty) *ts-unknown* *ts-empty* nil))
   ((equal x *nil*)
    (mv (or var :empty) *ts-empty* *ts-unknown* nil))
   ((fquotep x)
    (mv nil nil nil nil))
   ((flambda-applicationp x)
    (mv nil nil nil nil))
   ((eq (ffn-symb x) 'not)
    (mv-let (var not-true-ts not-false-ts runes)
      (strong-recognizer-expr-p var (fargn x 1) ens w)
      (mv var not-false-ts not-true-ts
          (if (and var (not (eq var :empty)))
              (add-to-set-equal '(:definition not) runes)
            runes))))
   ((and (fargs x) (not (cdr (fargs x))) ; optimization (else r below is nil)
         (or (eq var nil)
             (eq var :empty)
             (equal var (fargn x 1))))
    (let ((r (most-recent-enabled-recog-tuple (ffn-symb x) w ens)))
      (cond ((and r
                  (access recognizer-tuple r :strongp))
             (mv (fargn x 1)
                 (access recognizer-tuple r :true-ts)
                 (access recognizer-tuple r :false-ts)
                 (list (access recognizer-tuple r :rune))))
            (t (mv nil nil nil nil)))))
   (t (mv nil nil nil nil))))

(defun recognizer-expr-p (x ens w)

; X is a function symbol call (not a lambda application).  We return (mv var
; strongp true-ts false-ts rune[s]).  If var is nil then this call is
; considered to be a failure.  Otherwise either x is a call of a recognizer on
; var whose most-recent-enabled-recog-tuple has those strongp, true-ts, and
; false-ts fields, in which case var is :one and rune[s] is a single rune; or
; else x is a call of IF on a tree of strong compound-recognizer calls of var,
; in which case rune[s] is is a list of runes justifying that conclusion.

  (cond
   ((eq (ffn-symb x) 'if)
    (mv-let (var true-ts false-ts runes)
      (strong-recognizer-expr-p nil x ens w)
      (cond ((and var (not (eq var :empty)))
             (assert$ (ts= false-ts (ts-complement true-ts))
                      (mv var t true-ts false-ts runes)))
            (t (mv nil nil nil nil nil)))))
   ((and (fargs x) (not (cdr (fargs x)))) ; optimization
    (let ((r (most-recent-enabled-recog-tuple (ffn-symb x) w ens)))
      (cond (r (mv :one
                   (access recognizer-tuple r :strongp)
                   (access recognizer-tuple r :true-ts)
                   (access recognizer-tuple r :false-ts)
                   (access recognizer-tuple r :rune)))
            (t (mv nil nil nil nil nil)))))
   (t (mv nil nil nil nil nil))))

(defun push-lemma[s] (flg rune[s] ttree)

; Rune[s] is either a rune (flg=:one) or a duplicate-free list of runes.  In
; the latter case, we essentially iterate push-lemma, but by calling
; add-to-tag-tree just once.

  (cond ((eq flg :one)
         (push-lemma rune[s] ttree))
        (t (let ((pair (assoc-eq 'lemma ttree))
                 (runes (if (member-equal
                             *fake-rune-for-anonymous-enabled-rule*
                             rune[s])
                            (remove1-equal
                             *fake-rune-for-anonymous-enabled-rule*
                             rune[s])
                          rune[s])))
             (cond (pair (acons 'lemma
                                (union-equal runes (cdr pair))
                                (remove-tag-from-tag-tree! 'lemma ttree)))
                   (t (acons 'lemma runes ttree)))))))

(mutual-recursion

(defun type-set-rec (x force-flg dwp type-alist ancestors ens w ttree
                       pot-lst pt backchain-limit)

; X is a term and type-alist is a type alist mapping terms to their type-sets
; (and some ttrees) and thus encoding the current assumptions.  In a break with
; nqthm, the ACL2 type-set function tracks dependencies among the entries on
; the type-alist.  In particular, the type-alist here contains pairs of the
; form (term ts . ttree), where ttree is a tag-tree generally containing 'PT
; tags.  (There may be other tags, e.g., 'LEMMA and maybe even 'FC-DERIVATION
; during forward- chaining.)  In nqthm, the type-alist contained pairs of the
; form (term . ts).  The ttree argument to type-set is an accumulator onto
; which we add all of the ttrees attached to the facts we use from the
; type-alist and the wrld.  We return two results, the final type set of term
; and a ttree.

; Note:  If ancestors is t it means:  don't backchain.  Act as though
; the literal we're backchaining on is worse than everything in sight.
; This is called the ``t-ancestors hack'' and is commented upon below.

; Performance Notes:

; Type set was first made to track dependencies -- after a fashion --
; during the coding of forward chaining in April, 1990.  At that time,
; type-set had an option under which it would not track dependencies
; and that option was often used in rewrite; indeed, the only time
; dependencies were tracked was during setting up of the type-alist
; and forward chaining activations in simplify-clause.  In addition,
; compound recognizer lemmas were never tracked.  The paragraph below
; was written of that version of a ``dependency tracking'' type-set.

; Experiments show that (at the time of this writing) this type-set is
; roughly 30% slower than the type-set ACL2 had immediately before
; this addition.  That data was obtained by collecting roughly 70,000
; external calls of type-set that occurred during the proof that
; TAUTOLOGYP is sound and then timing their re-evaluation in both
; versions of ACL2 (with appropriate modifications of the type-alists
; being passed in).  That same experiment led to the surprising fact
; that type set may represent 50-75% of the time spent in the prover!

; We have since added full dependency tracking to type-set and have
; adopted the invariants on type-alist requiring canonical forms.  How
; much these changes slow things down is anyone's guess.  Stay tuned.

; The DWP flag
; or
; Performance Notes on the "Type-Set Objective" Idea and Double Whammy

; "DWP" stands for "double whammy flag".  It does not affect the
; soundness of the result returned but, when t, makes type-set "try
; harder" to get a narrow type.  It was added Feb 7, 1995 and replaces
; a heuristic hack controlling the "double whammy" idea.  The
; historical comment below explains.

; I have tried an experiment in which type-set gets the type of x in
; two ways and intersects them.  The first way is to look x up on the
; type-alist.  The second way is to compute it from scratch.  Call
; this the "double whammy" approach.  Double whammy is the simplest
; case of a more sophisticated type-set that computes a type for x
; relative to some specified "expected type."  The idea of that design
; was to have the caller of type-set supply the type it wanted x to
; have and type-set then did a double whammy if the type-alist type
; wasn't a subset of the expected type.  But that "conditional double
; whammy" idea is hard to implement.  For example, suppose you want (-
; a) to have a type-set of non-negative rational.  Then when you get
; the type-set of a you should want it to have type non-positive
; rational.  Rather than implement that fine tuned use of the expected
; type-set, I decided simply to implement the double whammy method,
; i.e., always using both ways and intersecting the results.  To my
; surprise, the double whammy method is 3 times slower than the
; ordinary type-set.  That number was obtained by running nqthm.lisp,
; which ordinarily takes 3460 seconds but which takes 10300 seconds
; under double whammy.  I then backed off the full blown double whammy
; and limited its use to the special case where (a) the type-set
; computed from the type-alist is negative and (b) forcing is allowed.
; Under these two cases, type-set is about 6% slower than without any
; double whammy processing.

; Why these two cases?  Here is the rationale I had, for what it is
; worth.  Condition (a) often indicates the type was "non-nil" or
; "anything but a negative", as when you assume (< 0 a) without
; knowing a is rational.  Presumably, forcing was disallowed when this
; negative binding was created, since we probably have forced
; hypotheses around to ensure that the guards are met.  Therefore, if
; condition (b) is also met, the chances are good that a "from
; scratch" computation will force now and we'll get a better answer.

; The hit rate even with these restrictions is quite unimpressive:
; double whammy changes the looked up type in only 1% of the cases
; where we try it!  Of the roughly 4.4 million calls of type-set in
; the nqthm.lisp proofs, 39% of them (1.7 million) find a binding on
; the type-alist and therefore check conditions (a) and (b).  In
; roughly 90% of the those cases, either the found type-set is
; negative or forcing is disallowed and so double whammy is not used.
; In only 176000 calls is double whammy even tried.  That is only 4%
; of the total number of type-set calls.  But of those 176000 attempts
; to use double whammy, in only 2254 cases did it help.  That's a 1%
; hit rate on double whammy.  Not really impressive.  However, one of
; those hits is the case that Bishop reported we couldn't prove and
; now we can.  That example is given below just for future reference.

;;; (progn (defstub foo (x) t)
;;;        (defun bar-p (x)
;;;          (consp x))
;;;        (in-theory (disable bar-p))
;;;        (defaxiom foo->=-0
;;;          (implies
;;;           (force (bar-p x))
;;;           (and (integerp (foo x))
;;;                (>= (foo x) 0)))
;;;          :rule-classes :type-prescription)
;;;        (defaxiom foo-bound
;;;          (implies
;;;           (force (bar-p x))
;;;           (< (foo x) 2))
;;;          :rule-classes (:linear :rewrite)))
;;;  (defthm test-foo-too
;;;    (not (< 1 (foo '(1 . 1)))))|#

; The problem is that (foo '(1 . 1)) is given the type-set
; non-negative anything when we construct the type-alist for the
; linear pot, because we do not force the (bar-p '(1 . 1)).  But
; later, when we are in linear we ask whether (foo '(1 . 1)) is an
; integer and, because of double whammy, force the previously unforced
; bar-p.

; Thus ends the historical comment.  Below, where (not dwp) is tested,
; we used to test
; (or (null force-flg)            ;;;(b)
;     (>= (the-type-set ts0) 0))  ;;;(a)

; This heuristic control on when to double whammy is thwarted by the
; example below.  Consider the clause shown below.  It ought to be
; decidable by type-set alone because if i is an integerp then (binary-+ '1 i)
; is too.  But the "irrelevant" hypothesis that (binary-+ '1 i) is a rationalp
; messes things up.  Let 1+i stand for the binary-+ expression.

; (type-alist-clause '((not (rationalp (binary-+ '1 i)))  ; lit 1
;                      (not (integerp i))                 ; lit 2
;                      (integerp (binary-+ '1 i)))        ; lit 3
;                     nil nil nil (ens state) (w state))

; We process lit 3 in a type-alist generated by assuming lits 1 and 2
; false.  In that type-alist, 1+i is assumed rational and i is assumed
; integral.  When we process lit 3, we get the type of 1+i.  Because of
; lit 1, we find it on the type-alist with rational type.  Because the
; type is non-negative we do not double whammy.  Thus, we miss the
; chance to use lit 2 in computing the type of 1+i.  We thus return a
; type-alist in which 1+i is assumed to be a ratio (non-integer
; rational) and i is integral.

; However, by arranging for assume-true-false always to call type-set
; with dwp = t, we make it use double whammy when assuming things.
; That allows us to catch this.  Our hope is that it does not slow us
; down too much.

  (mv-let
   (ts0 ttree0)
   (cond ((and (consp dwp)
               (eq (car dwp) :SKIP-LOOKUP))

; This case arises from reconsider-type-alist.  We found that by avoiding this
; lookup, we can avoid quadratic blow-up (distinct from the quadratic blow-up
; mentioned in a comment in reconsider-type-alist).  With this change, we saw a
; decrease of 20.1% in time spent for an example from Dave Greve.

          (mv (cadr dwp) (cddr dwp)))
         (t (assoc-type-alist x type-alist w)))
   (cond
    ((and ts0
          (or (not dwp)
              (and (consp dwp)
                   (not (eq (car dwp) :SKIP-LOOKUP))

; Dwp is a recognizer-tuple for some recognizer, fn; see the self-recursive
; call of type-set-rec below, just above the call of type-set-recognizer, for
; relevant explanation.  We are satisfied if this record decides whether an
; object of type ts0 definitely does, or does not, satisfy fn.  Objects whose
; type is disjoint from that of :true-ts must falsify fn, while those whose
; type is disjoint from that of :false-ts must satisfy fn; see
; recognizer-tuple.

                   (or (ts-disjointp
                        ts0
                        (access recognizer-tuple dwp :true-ts))
                       (ts-disjointp
                        ts0
                        (access recognizer-tuple dwp :false-ts))))))
     (mv ts0 (cons-tag-trees ttree ttree0)))
    ((variablep x)

; Warning: You may be tempted to change ttree below to nil on the
; grounds that we are not using any information about x to say its
; type is unknown.  But the specification for type-set is that ttree
; is an accumulator.  Our caller may have put a lot of work into
; deriving x and passed the associated ttree to type-set in good
; faith.  We are obliged to pass it on.

     (type-set-finish x ts0 ttree0 *ts-unknown* ttree type-alist))
    ((fquotep x)
     (type-set-finish x ts0 ttree0 (type-set-quote (cadr x)) ttree type-alist))
    ((flambda-applicationp x)

; Once upon a time, we tried to do this by using subcor-var to replace
; the actuals by the formals and then take the type-set of the body.
; The old code is shown, commented out, below.  But that was bad
; because it duplicated the actuals so often.  We now take the
; type-set of the body under a type-alist obtained from the actuals.
; We have to be careful to avoid forcing and use of the pot-lst.

     (mv-let (ts1 ttree1)
             (type-set-rec (lambda-body (ffn-symb x))
                           nil ; avoid forcing in lambda-body context
                           nil ; dwp
                           (zip-variable-type-alist
                            (lambda-formals (ffn-symb x))
                            (type-set-lst
                             (fargs x)
                             force-flg
                             nil ; dwp
                             type-alist ancestors ens w
                             pot-lst pt backchain-limit))

; Here is the motivation of the t-ancestors hack.  We cannot compare subterms
; of the lambda body to terms on the current ancestors because the lambda
; body should be instantiated with the actuals and it is not.  For example
; we might know (p x) on ancestors and go into ((lambda (x) (p x)) a) and
; mistakenly think the body is true because it is on ancestors.  (Ancestors
; is not used that way, but the point is made.)  So when ancestors is
; set to t it means ignore ancestors and don't backchain.  The type-set
; clique is the only nest of functions that treats ancestors that way.

; Here is the one place we initiate the t-ancestors hack.

                           t ;;; t-ancestors hack
                           ens w ttree

; The pot-lst is not valid in the current context, because the body is not
; instantiated with the actuals.  So we replace it with nil.

                           nil
                           pt
                           backchain-limit)
             (type-set-finish x ts0 ttree0 ts1 ttree1 type-alist)))

;     ((flambda-applicationp x)

; Note: Once upon a time, assumptions only recorded the term forced and not the
; type-alist involved.  We could get away with that because rewrite-atm would
; recover all the assumptions and force a case split on the whole clause to
; handle them.  During those simple days, we treated lambda expressions
; efficiently here, by computing the type-set of the lambda-body under a
; type-alist binding the lambda-formals to the types of the actuals.
; Afterwards, we swept the ttree and appropriately instantiated the forced
; terms with the actuals.  But when we introduced assumption records, with the
; type-alists recorded in them, this design became problematic: we would have
; had to instantiate the :type-alists too.  Rather than do so, we abandoned
; efficiency here and did the obvious:  we expanded lambda applications
; by substituting actuals for formals in the body and computed the type-set
; of the result.  This survived until Version  2.6.

;;;      (mv-let (ts1 ttree1)
;;;              (type-set-rec (subcor-var (lambda-formals (ffn-symb x))
;;;                                    (fargs x)
;;;                                    (lambda-body (ffn-symb x)))
;;;                        force-flg
;;;                        nil ; dwp
;;;                        type-alist
;;;                        ancestors
;;;                        ens w ttree pot-lst pt backchain-limit)
;;;              (type-set-finish x ts0 ttree0 ts1 ttree1 type-alist))

; The following historical comment comes from when we supported the nu-rewriter
; (which has since been eliminated).  Perhaps it is worth revisiting the
; decision described below.

;   When we introduced the nu-rewriter, we made clausify no longer
;   expand lambdas so aggressively.  This meant that type-set began to
;   see a lot more lambdas.  In that environment, the expansion of lambdas
;   here was taking lot of time and generating a lot of conses.  So now
;   we take the efficient AND brain-dead approach of saying we simply
;   don't know anything about a lambda application.

;      (type-set-finish x ts0 ttree0 *ts-unknown* ttree type-alist))

    ((eq (ffn-symb x) 'not)
     (mv-let (ts1 ttree1)
             (type-set-rec (fargn x 1) force-flg
                           nil ; dwp
                           type-alist ancestors
                           ens w ttree pot-lst pt backchain-limit)
             (mv-let (ts1 ttree1)
                     (type-set-not ts1 ttree1 ttree)
                     (type-set-finish x ts0 ttree0 ts1 ttree1 type-alist))))
    (t
     (let* ((fn (ffn-symb x))
            (recog-tuple (most-recent-enabled-recog-tuple fn w ens))
            (dwp (if (and (consp dwp) (eq (car dwp) :SKIP-LOOKUP))
                     nil
                   dwp)))
       (cond
        (recog-tuple
         (mv-let
          (ts1 ttree1)
          (type-set-rec (fargn x 1) force-flg
                        (and (or force-flg dwp)

; The example below, essentially from Jared Davis, motivates our passing a
; non-nil value of dwp here.

; (progn
;   (defstub foo-p (x) t)
;   (defstub bar-p (x) t)
;   (defstub foo->field (x) t)
;   (defaxiom foo-p-type
;     (booleanp (foo-p x))
;     :rule-classes :type-prescription)
;   (defaxiom bar-p-type
;     (booleanp (bar-p x))
;     :rule-classes :type-prescription)
;   (defaxiom foo->field-type
;     (implies (force (foo-p x))
;              (or (stringp (foo->field x))
;                  (not (foo->field x))))
;     :rule-classes :type-prescription)
;   (defaxiom bar-p-when-stringp
;     (implies (stringp x)
;              (bar-p x))))

; We then would like to see a forcing round for the following.  But we don't
; get that if we use dwp=nil, as was done through Version_4.1.

; (thm (implies (foo->field x)
;               (bar-p (foo->field x))))

; But we do not pass recog-tuple in every case -- see (or force-flg dwp) above
; -- because that causes significant slowdown.  Here are some statistics on the
; regression suite, using a development version of ACL2 in early November,
; 2010, running with 'make' option "-j 4" on a 2-core multi-threaded MacBook
; Pro i7.

; Before any change:

;   real  83m26.179s
;   user 276m28.269s
;   sys   17m16.883s

; New version:

;   real  83m11.087s
;   user 277m13.043s
;   sys  17m21.616s

; Using dwp=t here, with Version_4.1 code just under assoc-type-alist near the
; top of this function:

;   real 104m24.803s
;   user 303m7.784s
;   sys   17m59.079s

; Using dwp=recog-tuple here, with the same new code just under
; assoc-type-alist near the top of this function, but without conditionalizing
; on (or force-flg dwp).  (Did two timings in case the machine went to sleep
; during the first.)

;   real 103m17.474s / 102m48.885s
;   user 299m40.781s / 300m32.856s
;   sys   18m5.536s  /  18m6.812s

; Finally, we remark on why we conditionalize above on the disjunction (or
; force-flg dwp).  A non-nil value of dwp seems an appropriate reason to
; propagate a double-whammy heuristic to the argument of a recognizer.  But
; that alone doesn't suffice for Jared's example; however, force-flg does.  The
; dwp and force-flg parameters seem like the obvious conditions for enabling
; the use of recog-tuple for dwp, and proofs don't noticeably slow down when
; using their disjunction; so that is what we do.

                             recog-tuple)
                        type-alist ancestors
                        ens w ttree pot-lst pt backchain-limit)
          (mv-let
           (ts1 ttree1)
           (type-set-recognizer recog-tuple ts1 ttree1 ttree)
           (mv-let (ts ttree)
                   (type-set-finish x ts0 ttree0 ts1 ttree1 type-alist)

; At this point, ts is the intersection of the type-alist information and the
; recog information.  Unless ts is t or nil we also try any type-prescription
; rules we have about this function symbol.

                   (cond
                    ((or (ts= ts *ts-t*)
                         (ts= ts *ts-nil*))
                     (mv ts ttree))
                    (t

; WARNING: There is another call of type-set-with-rules below, in the normal
; case.  This call is for the recognizer function case.  If you change this
; one, change that one!

                     (mv-let
                      (ts2 ttree2 extended-p)
                      (type-set-with-rules
                       (getpropc fn 'type-prescriptions nil w)
                       x force-flg
                       dwp ; see comment in rewrite-atm about "use of dwp"
                       type-alist ancestors ens w
                       *ts-unknown* ttree pot-lst pt backchain-limit nil)
                      (declare (ignore extended-p))
                      (mv (ts-intersection ts ts2) ttree2))))))))
        ((eq fn 'if)

; It is possible that the if-expression x is on the type-alist. It
; would get there if we had gone through an earlier assume-true-false
; on x, i.e., if we were processing b in (if (if x1 x2 x3) b c).  So
; we will compute the type-set of x directly based on its structure
; and then finish as usual by anding it with ts0, the type-set of x
; itself as recorded on the type-alist, as appropriate.

         (mv-let
          (ts1 ttree1)
          (mv-let
           (must-be-true
            must-be-false
            true-type-alist
            false-type-alist
            ttree1)
           (assume-true-false-rec (fargn x 1)
                                  nil
                                  force-flg
                                  nil ; dwp
                                  type-alist
                                  ancestors
                                  ens
                                  w
                                  pot-lst pt nil
                                  backchain-limit)

; If must-be-true or must-be-false is set, then ttree1 explains the
; derivation of that result.  If neither is derived, then ttree1 is
; nil and we can ignore it.

           (cond (must-be-true
                  (cond (must-be-false

; We have a contradictory context.  See the discussion about "contradictory
; context" in assume-true-false to see where it returns t for both must-be-true
; and must-be-false.  This case allows improved type-prescription inference as
; shown below; before we both modified this function and modified
; assume-true-false to be able to return must-be-true = must-be-false = t, it
; failed.  Note that without the force, there are two separate hypotheses on
; natp-logior rather than (if (natp x) (natp y) 'nil).

;   (skip-proofs ; to avoid bothering to prove this with arithmetic-5
;    (defthm natp-logior
;      (implies (force (and (natp x) (natp y)))
;               (natp (logior x y)))
;      :rule-classes :type-prescription))
;
;   (defun foo (x)
;     (cond
;      ((consp x)
;       (logior (foo (car x))
;               (foo (cdr x))))
;      (t 0)))
;
;   ; This is *ts-non-negative-integer*, but formerly it was *ts-integer*.
;   (caar (getpropc 'foo 'type-prescriptions))

                         (mv *ts-empty* (cons-tag-trees ttree1 ttree)))
                        (t (type-set-rec (fargn x 2)
                                         force-flg
                                         nil ; dwp
                                         true-type-alist
                                         ancestors
                                         ens
                                         w
                                         (cons-tag-trees ttree1 ttree)
                                         pot-lst pt backchain-limit))))
                 (must-be-false
                  (type-set-rec (fargn x 3)
                                force-flg
                                nil ; dwp
                                false-type-alist
                                ancestors
                                ens
                                w
                                (cons-tag-trees ttree1 ttree)
                                pot-lst pt backchain-limit))
                 (t (mv-let (ts1 ttree)
                            (type-set-rec (fargn x 2)
                                          force-flg
                                          nil ; dwp
                                          true-type-alist
                                          ancestors
                                          ens
                                          w
                                          ttree
                                          pot-lst pt backchain-limit)
                            (mv-let (ts2 ttree)
                                    (type-set-rec (fargn x 3)
                                                  force-flg
                                                  nil ; dwp
                                                  false-type-alist
                                                  ancestors
                                                  ens
                                                  w
                                                  ttree
                                                  pot-lst pt
                                                  backchain-limit)
                                    (mv (ts-union ts1 ts2)
                                        ttree))))))
          (type-set-finish x ts0 ttree0 ts1 ttree1 type-alist)))
        ((member-eq fn *expandable-boot-strap-non-rec-fns*)

; For these particular functions we actually substitute the actuals
; for the formals into the guarded body and dive into the body to get
; the answer.  Typically we will not ever encounter these functions in
; proofs because they will have been expanded away.  However, we will
; encounter them during the early type-prescription work and
; pre-verify-guard work, and so think it is worthwhile to handle them.

         (mv-let (ts1 ttree1)
                 (type-set-rec (subcor-var (formals fn w)
                                           (fargs x)
                                           (bbody fn))
                               force-flg
                               nil ; dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree
                               pot-lst pt
                               backchain-limit)
                 (type-set-finish x ts0 ttree0 ts1 ttree1 type-alist)))
        (t

; Otherwise, we apply all known type-prescriptions and conclude with
; whatever is built in about fn.

; Note: We do not know that 'type-prescriptions is non-nil.  Once upon
; a time we insisted that every fn have a type-prescription.  This
; complicated the defun principle because one might encounter the
; unadmitted function symbol in the termination proofs (e.g.,
; mc-flatten).  So now we are lenient.  This happens to be what Nqthm
; does too, and now we know why!

; WARNING:  There is another call of type-set-with-rules above, in the
; recog-tuple case.  If you change this one, change that one!

         (mv-let (ts1 ttree1 extended-p)
                 (type-set-with-rules
                  (getpropc fn 'type-prescriptions nil w)
                  x force-flg
                  dwp ; see comment in rewrite-atm about "use of dwp"
                  type-alist ancestors ens w
                  *ts-unknown* ttree
                  pot-lst pt backchain-limit nil)
                 (declare (ignore extended-p))
                 (type-set-finish x ts0 ttree0 ts1 ttree1
                                  type-alist)))))))))

(defun type-set-lst (x force-flg dwp type-alist ancestors ens w
                     pot-lst pt backchain-limit)

; This function computes the type-set of each element of x, obtaining for each
; a ts and a ttree.  It conses the two together and makes a list of those pairs
; in 1:1 correspondence with x.  That is, if x is (x1 ... xn) then the answer,
; ans, is ((ts1 . ttree1) ... (tsn .  ttreen)).  (Strip-cars ans) will return a
; list of the type sets and (strip-cdrs ans) will return a list of the ttrees.
; Furthermore, if x is a list of variables, (zip-variable-type-alist x ans)
; will return a type-alist!

  (cond
   ((null x) nil)
   (t (mv-let (ts ttree)
              (type-set-rec (car x) force-flg dwp type-alist ancestors ens w
                            nil pot-lst pt backchain-limit)
              (cons (cons ts ttree)
                    (type-set-lst (cdr x)
                                  force-flg dwp type-alist ancestors ens w
                                  pot-lst pt backchain-limit))))))

(defun type-set-relieve-hyps-free (term typ rest-type-alist
                                        rune target hyps backchain-limit-lst
                                        force-flg dwp alist type-alist
                                        ancestors ens wrld ttree ttree0 pot-lst pt
                                        backchain-limit bkptr+1)

  (assert$
   rest-type-alist
   (mv-let
    (lookup-hyp-ans alist+ ttree rest-type-alist)
    (search-type-alist-with-rest term typ rest-type-alist alist ttree wrld)
    (cond
     ((null lookup-hyp-ans) (mv nil type-alist ttree0))
     ((null rest-type-alist) ; optimization (prefer this tail call)
      (type-set-relieve-hyps rune
                             target
                             (cdr hyps)
                             (cdr backchain-limit-lst)
                             force-flg dwp alist+
                             type-alist ancestors ens wrld
                             ttree ttree0
                             pot-lst pt backchain-limit
                             bkptr+1))
     (t ; lookup-hyp-ans and non-nil new value of rest-type-alist
      (mv-let
       (relieve-hyps-ans type-alist ttree)
       (type-set-relieve-hyps rune
                              target
                              (cdr hyps)
                              (cdr backchain-limit-lst)
                              force-flg dwp alist+
                              type-alist ancestors ens wrld
                              ttree ttree0
                              pot-lst pt backchain-limit
                              bkptr+1)
       (cond
        (relieve-hyps-ans (mv relieve-hyps-ans type-alist ttree))
        (t (type-set-relieve-hyps-free term typ rest-type-alist
                                       rune target hyps backchain-limit-lst
                                       force-flg dwp alist type-alist
                                       ancestors ens wrld ttree ttree0 pot-lst pt
                                       backchain-limit bkptr+1)))))))))

(defun type-set-relieve-hyps1 (hyp forcep rune target hyps backchain-limit-lst
                                   force-flg dwp alist type-alist ancestors ens
                                   wrld ttree ttree0 pot-lst pt backchain-limit
                                   bkptr)
  (mv-let
   (not-flg atm)
   (strip-not hyp)
   (mv-let
    (atm1 quotep-atm1 ttree)
    (sublis-var! alist atm ens wrld ttree)

; Note that we stripped off the force (or case-split) symbol if it was
; present.  We don't have to do that (given that the type-set of
; (force x) and of (case-split x) is known to be that of x) but it ought
; to speed things up slightly.  Note that we also stripped off the NOT
; if it was present and have not-flg and the instantiated atom, atm1,
; to work on.  We work on the atom so that we can record its type-set
; in the final type-alist, rather than recording the type-set of (NOT
; atm1).

    (cond
     (quotep-atm1
      (cond ((eq not-flg (equal atm1 *nil*))
             (type-set-relieve-hyps rune
                                    target
                                    (cdr hyps)
                                    (cdr backchain-limit-lst)
                                    force-flg dwp alist
                                    type-alist ancestors ens wrld
                                    ttree ttree0
                                    pot-lst pt backchain-limit
                                    (1+ bkptr)))
            (t (mv nil type-alist ttree0))))
     (t
      (mv-let
       (on-ancestorsp assumed-true)

; Here is the one place where we (potentially) use the t-ancestors
; hack to abort early.

       (if (eq ancestors t)
           (mv t nil)
         (ancestors-check (if not-flg
                              (mcons-term* 'not atm1)
                            atm1)
                          ancestors
                          (list rune)))
       (cond
        (on-ancestorsp
         (cond
          (assumed-true
           (type-set-relieve-hyps rune
                                  target
                                  (cdr hyps)
                                  (cdr backchain-limit-lst)
                                  force-flg dwp alist
                                  type-alist ancestors ens wrld
                                  ttree ttree0
                                  pot-lst pt backchain-limit
                                  (1+ bkptr)))
          (t (mv nil type-alist ttree0))))
        ((backchain-limit-reachedp backchain-limit ancestors)
         (mv-let
          (force-flg ttree)
          (cond
           ((not (and force-flg forcep))
            (mv nil ttree))
           (t (force-assumption
               rune
               target
               (if not-flg
                   (mcons-term* 'not atm1)
                 atm1)
               type-alist nil
               (immediate-forcep
                (ffn-symb (car hyps))
                ens)
               force-flg
               ttree)))
          (cond
           (force-flg
            (type-set-relieve-hyps
             rune
             target
             (cdr hyps)
             (cdr backchain-limit-lst)
             force-flg dwp alist type-alist ancestors
             ens wrld ttree ttree0 pot-lst pt
             backchain-limit (1+ bkptr)))
           (t (mv nil type-alist ttree0)))))
        (t
         (mv-let
          (flg type-alist ttree2)
          (with-accumulated-persistence
           rune
           (flg type-alist ttree2)
           flg
           (mv-let
            (ts1 ttree1)
            (type-set-rec atm1 force-flg dwp type-alist

; We know ancestors is not t here, by the tests above.

                          (push-ancestor
                           (if not-flg
                               atm1
                             (mcons-term* 'not atm1))
                           (list rune)
                           ancestors
                           nil)
                          ens wrld ttree
                          pot-lst pt
                          (new-backchain-limit
                           (car backchain-limit-lst)
                           backchain-limit
                           ancestors))
            (let ((ts (if not-flg
                          (cond ((ts= ts1 *ts-nil*) *ts-t*)
                                ((ts-intersectp ts1 *ts-nil*)
                                 *ts-boolean*)
                                (t *ts-nil*))
                        ts1)))
              (cond
               ((ts= ts *ts-nil*) (mv nil type-alist ttree0))
               ((ts-intersectp *ts-nil* ts)
                (mv-let
                 (force-flg ttree)
                 (cond
                  ((not (and force-flg forcep))
                   (mv nil ttree))
                  (t (force-assumption
                      rune
                      target
                      (if not-flg
                          (mcons-term* 'not atm1)
                        atm1)
                      type-alist nil
                      (immediate-forcep
                       (ffn-symb (car hyps))
                       ens)
                      force-flg
                      ttree)))
                 (cond
                  (force-flg (mv t type-alist ttree))
                  (t (mv nil type-alist ttree0)))))
               (t (mv t type-alist ttree1)))))
           bkptr)
          (cond (flg (type-set-relieve-hyps
                      rune
                      target
                      (cdr hyps)
                      (cdr backchain-limit-lst)
                      force-flg dwp alist type-alist ancestors
                      ens wrld ttree2 ttree0 pot-lst pt
                      backchain-limit (1+ bkptr)))
                (t (mv nil type-alist ttree2))))))))))))

(defun type-set-relieve-hyps (rune target hyps backchain-limit-lst
                                   force-flg dwp alist type-alist
                                   ancestors ens wrld ttree ttree0 pot-lst pt
                                   backchain-limit bkptr)

; Hyps is a list of terms, implicitly conjoined.  Alist is a substitution
; mapping variables in hyps to terms governed by type-alist.  Consider the
; result, hyps', of substituting alist into each hyp in hyps.  We wish to know
; whether, by type-set reasoning alone, we can get that hyps' are all true in
; the context of type-alist.  We do the substitution one hyp at a time, so we
; don't pay the price of consing up instances beyond the first hyp that fails.
; While we are at it, we record in an extension of type-alist the type computed
; for each hyp', so that if subsequent rules need that information, they can
; get it quickly.

; No Change Loser for ttree, but not for type-alist.

  (cond
   ((null hyps) (mv t type-alist (cons-tag-trees ttree ttree0)))
   (t (mv-let
       (forcep bind-flg)
       (binding-hyp-p (car hyps) alist wrld)
       (let ((hyp (if forcep
                      (fargn (car hyps) 1)
                    (car hyps))))
         (cond
          (bind-flg
           (type-set-relieve-hyps
            rune target (cdr hyps) (cdr backchain-limit-lst)
            force-flg dwp
            (cons (cons (fargn hyp 1) (fargn hyp 2)) alist)
            type-alist ancestors ens wrld ttree ttree0
            pot-lst pt backchain-limit (1+ bkptr)))
          (t
           (mv-let
            (term typ compound-rec-rune?)
            (term-and-typ-to-lookup hyp wrld ens)
            (mv-let
             (lookup-hyp-ans alist+ ttree rest-type-alist)
             (search-type-alist-with-rest term typ type-alist alist ttree wrld)
             (cond
              (lookup-hyp-ans
               (let ((ttree (push-lemma? compound-rec-rune? ttree)))
                 (cond
                  ((and rest-type-alist
                        (not (eq (caar alist) (caar alist+))) ; free vars
                        (not (oncep-tp rune wrld)))
                   (let ((bkptr+1 (1+ bkptr)))
                     (mv-let
                       (relieve-hyps-ans type-alist ttree)
                       (type-set-relieve-hyps rune
                                              target
                                              (cdr hyps)
                                              (cdr backchain-limit-lst)
                                              force-flg dwp alist+
                                              type-alist ancestors ens wrld
                                              ttree ttree0
                                              pot-lst pt backchain-limit
                                              bkptr+1)
                       (cond
                        (relieve-hyps-ans (mv relieve-hyps-ans type-alist ttree))
                        (t (type-set-relieve-hyps-free
                            term typ rest-type-alist
                            rune target hyps backchain-limit-lst
                            force-flg dwp alist type-alist
                            ancestors ens wrld ttree ttree0 pot-lst pt
                            backchain-limit bkptr+1))))))
                  (t (type-set-relieve-hyps rune
                                            target
                                            (cdr hyps)
                                            (cdr backchain-limit-lst)
                                            force-flg dwp alist+
                                            type-alist ancestors ens wrld
                                            ttree ttree0
                                            pot-lst pt backchain-limit
                                            (1+ bkptr))))))
              ((free-varsp hyp alist)
               (let ((fully-bound-alist
                      (if (and forcep force-flg)
                          (bind-free-vars-to-unbound-free-vars
                           (all-vars hyp)
                           alist)
                        alist)))

; Fully-bound-alist is an extension of alist in which all vars occurring
; in hyp are bound to something.  A var v that occurs freely in hyp wrt
; alist is bound in fully-bound-alist to UNBOUND-FREE-v.  But we only
; compute the all-vars and fully-bound-alist if we're going to use it
; below.  For sanity, fully-bound-alist is just alist if we're not
; actually intending to use it.

                 (mv-let
                  (force-flg ttree)
                  (cond
                   ((not (and forcep force-flg))
                    (mv nil ttree))
                   (t (force-assumption
                       rune
                       target
                       (sublis-var fully-bound-alist hyp)
                       type-alist
                       nil
                       (immediate-forcep (ffn-symb (car hyps)) ens)
                       force-flg
                       ttree)))

; Note that force-flg has been rebound by the mv-let above.  Think of
; it as just a temporary variable meaning (and forcep force-flg) and
; we use it only if it is true.

                  (cond
                   (force-flg
                    (type-set-relieve-hyps
                     rune target (cdr hyps) (cdr backchain-limit-lst)
                     force-flg dwp
                     fully-bound-alist type-alist ancestors ens wrld
                     ttree ttree0
                     pot-lst pt backchain-limit (1+ bkptr)))
                   (t (mv nil type-alist ttree0))))))
              (t
               (mv-let
                (not-flg atm)
                (strip-not hyp)
                (mv-let
                 (atm1 quotep-atm1 ttree)
                 (sublis-var! alist atm ens wrld ttree)

; Note that we stripped off the force (or case-split) symbol if it was
; present.  We don't have to do that (given that the type-set of
; (force x) and of (case-split x) is known to be that of x) but it ought
; to speed things up slightly.  Note that we also stripped off the NOT
; if it was present and have not-flg and the instantiated atom, atm1,
; to work on.  We work on the atom so that we can record its type-set
; in the final type-alist, rather than recording the type-set of (NOT
; atm1).

                 (cond
                  (quotep-atm1
                   (cond ((eq not-flg (equal atm1 *nil*))
                          (type-set-relieve-hyps rune
                                                 target
                                                 (cdr hyps)
                                                 (cdr backchain-limit-lst)
                                                 force-flg dwp alist
                                                 type-alist ancestors ens wrld
                                                 ttree ttree0
                                                 pot-lst pt backchain-limit
                                                 (1+ bkptr)))
                         (t (mv nil type-alist ttree0))))
                  (t
                   (mv-let
                    (on-ancestorsp assumed-true)

; Here is the one place where we (potentially) use the t-ancestors
; hack to abort early.

                    (if (eq ancestors t)
                        (mv t nil)
                      (ancestors-check (if not-flg
                                           (mcons-term* 'not atm1)
                                         atm1)
                                       ancestors
                                       (list rune)))
                    (cond
                     (on-ancestorsp
                      (cond
                       (assumed-true
                        (type-set-relieve-hyps rune
                                               target
                                               (cdr hyps)
                                               (cdr backchain-limit-lst)
                                               force-flg dwp alist
                                               type-alist ancestors ens wrld
                                               ttree ttree0
                                               pot-lst pt backchain-limit
                                               (1+ bkptr)))
                       (t (mv nil type-alist ttree0))))
                     ((backchain-limit-reachedp backchain-limit ancestors)
                      (mv-let
                       (force-flg ttree)
                       (cond
                        ((not (and force-flg forcep))
                         (mv nil ttree))
                        (t (force-assumption
                            rune
                            target
                            (if not-flg
                                (mcons-term* 'not atm1)
                              atm1)
                            type-alist nil
                            (immediate-forcep
                             (ffn-symb (car hyps))
                             ens)
                            force-flg
                            ttree)))
                       (cond
                        (force-flg
                         (type-set-relieve-hyps
                          rune
                          target
                          (cdr hyps)
                          (cdr backchain-limit-lst)
                          force-flg dwp alist type-alist ancestors
                          ens wrld ttree ttree0 pot-lst pt
                          backchain-limit (1+ bkptr)))
                        (t (mv nil type-alist ttree0)))))
                     (t
                      (mv-let
                       (flg type-alist ttree2)
                       (with-accumulated-persistence
                        rune
                        (flg type-alist ttree2)
                        flg
                        (mv-let
                         (ts1 ttree1)
                         (type-set-rec atm1 force-flg dwp type-alist

; We know ancestors is not t here, by the tests above.

                                       (push-ancestor
                                        (if not-flg
                                            atm1
                                          (mcons-term* 'not atm1))
                                        (list rune)
                                        ancestors
                                        nil)
                                       ens wrld ttree
                                       pot-lst pt
                                       (new-backchain-limit
                                        (car backchain-limit-lst)
                                        backchain-limit
                                        ancestors))
                         (let ((ts (if not-flg
                                       (cond ((ts= ts1 *ts-nil*) *ts-t*)
                                             ((ts-intersectp ts1 *ts-nil*)
                                              *ts-boolean*)
                                             (t *ts-nil*))
                                     ts1)))
                           (cond
                            ((ts= ts *ts-nil*) (mv nil type-alist ttree0))
                            ((ts-intersectp *ts-nil* ts)
                             (mv-let
                              (force-flg ttree)
                              (cond
                               ((not (and force-flg forcep))
                                (mv nil ttree))
                               (t (force-assumption
                                   rune
                                   target
                                   (if not-flg
                                       (mcons-term* 'not atm1)
                                     atm1)
                                   type-alist nil
                                   (immediate-forcep
                                    (ffn-symb (car hyps))
                                    ens)
                                   force-flg
                                   ttree)))
                              (cond
                               (force-flg (mv t type-alist ttree))
                               (t (mv nil type-alist ttree0)))))
                            (t (mv t type-alist ttree1)))))
                        bkptr)
                       (cond (flg (type-set-relieve-hyps
                                   rune
                                   target
                                   (cdr hyps)
                                   (cdr backchain-limit-lst)
                                   force-flg dwp alist type-alist ancestors
                                   ens wrld ttree2 ttree0 pot-lst pt
                                   backchain-limit (1+ bkptr)))
                             (t (mv nil type-alist ttree2))))))))))))))))))))))

(defun extend-type-alist-with-bindings (alist force-flg dwp type-alist
                                              ancestors ens w ttree pot-lst pt
                                              backchain-limit)

; Alist is an alist that pairs variables in some rule with terms.  We compute
; the type-set of each term in the range of alist and extend type-alist with
; new entries that pair each term to its type-set.

  (cond ((null alist) type-alist)
        (t (extend-type-alist-with-bindings
            (cdr alist)
            force-flg
            dwp
            (cond ((assoc-equal (cdr (car alist)) type-alist)
                   type-alist)
                  (t
                   (mv-let (ts ttree1)
                           (type-set-rec (cdr (car alist))
                                         force-flg dwp type-alist ancestors ens
                                         w ttree pot-lst pt backchain-limit)
                           (extend-type-alist
                            ;;*** -simple
                            (cdr (car alist)) ts ttree1 type-alist w))))
            ancestors
            ens w ttree
            pot-lst pt backchain-limit))))

(defun type-set-with-rule (tp term force-flg dwp type-alist ancestors ens w
                              ttree pot-lst pt backchain-limit extended-p)

; We apply the type-prescription, tp, to term, if possible, and return a
; type-set, an extended type-alist and a ttree.  If the rule is inapplicable,
; the type-set is *ts-unknown* and the ttree is unchanged.  Recall that
; type-set treats its ttree argument as an accumulator and we are obliged to
; return an extension of the input ttree.

; Note that the specification of this function is that if we were to take the
; resulting type-alist and cons the input ttree on to each ttree in that
; type-alist, the resulting type-alist would be "appropriate".  In particular,
; we don't put ttree into the type-alist, but instead we assume that our caller
; will compensate appropriately.

  (declare (ignore dwp))
  (cond
   ((enabled-numep (access type-prescription tp :nume) ens)
    (mv-let
     (unify-ans unify-subst)
     (one-way-unify (access type-prescription tp :term)
                    term)
     (cond
      (unify-ans
       (with-accumulated-persistence
        (access type-prescription tp :rune)
        (ts type-alist-out ttree-out extended-p-out)
        (or (not (ts= *ts-unknown* ts))

; The following mis-guarded use of eq instead of equal implies that we could be
; over-counting successes at the expense of failures.

            (not (eq type-alist type-alist-out)))
        (let ((hyps (access type-prescription tp :hyps)))
          (mv-let
            (type-alist extended-p)
            (cond
             ((or (null hyps)
                  extended-p)
              (mv type-alist extended-p))
             (t (mv (extend-type-alist-with-bindings
                     unify-subst
                     force-flg
                     nil ; dwp
                     type-alist
                     ancestors
                     ens w

; We lie here by passing in the nil tag-tree, so that we can avoid
; contaminating the resulting type-alist with a copy of ttree.  We'll make sure
; that ttree gets into the answer returned by type-alist-with-rules, which is
; the only function that calls type-set-with-rule.

                     nil
                     pot-lst pt
                     backchain-limit)
                    t)))
            (mv-let
              (relieve-hyps-ans type-alist ttree)
              (type-set-relieve-hyps (access type-prescription tp :rune)
                                     term
                                     hyps
                                     (access type-prescription tp
                                             :backchain-limit-lst)
                                     force-flg
                                     nil ; dwp
                                     unify-subst
                                     type-alist
                                     ancestors
                                     ens w

; We pass in nil here to avoid contaminating the type-alist returned by this
; call of type-set-relieve-hyps.

                                     nil
                                     ttree
                                     pot-lst pt backchain-limit 1)
              (cond
               (relieve-hyps-ans
                (mv-let
                  (ts type-alist ttree)
                  (with-accumulated-persistence
                   (access type-prescription tp :rune)
                   (ts type-alist-out ttree)
                   (or (not (ts= *ts-unknown* ts))

; The following mis-guarded use of eq instead of equal implies that we could be
; over-counting successes at the expense of failures.

                       (not (eq type-alist type-alist-out)))
                   (type-set-with-rule1
                    unify-subst
                    (access type-prescription tp :vars)
                    force-flg
                    nil ; dwp
                    type-alist ancestors ens w
                    (access type-prescription tp :basic-ts)
                    (push-lemma
                     (access type-prescription tp :rune)
                     ttree)
                    pot-lst pt backchain-limit)
                   :conc
                   hyps)
                  (mv ts type-alist ttree extended-p)))
               (t (mv *ts-unknown* type-alist ttree extended-p))))))))
      (t (mv *ts-unknown* type-alist ttree nil)))))
   (t (mv *ts-unknown* type-alist ttree nil))))

(defun type-set-with-rule1 (alist vars force-flg dwp type-alist ancestors ens w
                                  basic-ts ttree pot-lst pt backchain-limit)

; Alist is an alist that maps variables to terms.  The terms are in the context
; described by type-alist.  Vars is a list of variables.  We map over the pairs
; in alist unioning into basic-ts the type-sets of those terms whose
; corresponding vars are in vars.  We accumulate the ttrees into ttree and
; ultimately return the final basic-ts, type-alist and ttree.  The alist
; contains successive formals paired with actuals.

; We are about to return from type-set-with-rule with the type-set of
; a term, say (foo x), as indicated by a :type-prescription rule, say
; ts-foo, but we are not quite done yet.  On the initial entry to this
; function, basic-ts and vars are from the corresponding fields of
; ts-foo.  Vars is a (possibly empty) subset of the variables in
; ts-foo.  The meaning of ts-foo is that the type-set of (foo x) is
; the union of basic-ts and the types of (the terms bound to) vars.
; See the definition of a type-prescription rule and surrounding
; discussion.  (Search for ``defrec type-prescription'' in this file.)

  (cond ((null alist) (mv basic-ts type-alist ttree))
        ((member-eq (caar alist) vars)
         (mv-let (ts ttree)
                 (type-set-rec
                  (cdar alist) force-flg dwp type-alist ancestors ens w ttree
                  pot-lst pt backchain-limit)
                 (type-set-with-rule1 (cdr alist) vars force-flg dwp
                                      type-alist ancestors ens w
                                      (ts-union ts basic-ts)
                                      ttree
                                      pot-lst pt backchain-limit)))
        (t (type-set-with-rule1 (cdr alist) vars force-flg dwp
                                type-alist ancestors ens w
                                basic-ts
                                ttree
                                pot-lst pt backchain-limit))))

(defun type-set-with-rules (tp-lst term force-flg dwp type-alist ancestors ens
                            w ts ttree pot-lst pt backchain-limit extended-p)

; We try to apply each type-prescription in tp-lst, intersecting
; together all the type sets we get and accumulating all the ttrees.
; However, if a rule fails to change the accumulating type-set, we
; ignore its ttree.

  (cond
   ((null tp-lst)
    (mv-let
     (ts1 ttree1)
     (type-set-primitive term force-flg dwp type-alist ancestors ens w ttree
                         pot-lst pt backchain-limit)
     (let ((ts2 (ts-intersection ts1 ts)))
       (mv ts2 (if (ts= ts2 ts) ttree ttree1) extended-p))))
   ((ts-subsetp ts
                (access type-prescription (car tp-lst) :basic-ts))

; Our goal is to make the final type-set, ts, as small as possible by
; intersecting it with the type-sets returned to the various rules.  If ts is
; already smaller than or equal to the :basic-ts of a rule, there is no point
; in trying that rule: the returned type-set will be at least as large as
; :basic-ts (it has the :vars types unioned into it) and then when we intersect
; ts with it we'll just get ts back.  The original motivation for this
; short-cut was to prevent the waste of time caused by the
; pre-guard-verification type-prescription if the post-guard-verification rule
; is present.

    (type-set-with-rules (cdr tp-lst)
                         term force-flg dwp type-alist ancestors ens w ts ttree
                         pot-lst pt backchain-limit extended-p))
   (t
     (mv-let
       (ts1 type-alist1 ttree1 extended-p)
       (type-set-with-rule (car tp-lst)
                           term force-flg dwp type-alist ancestors ens w ttree
                           pot-lst pt backchain-limit extended-p)
       (let ((ts2 (ts-intersection ts1 ts)))
         (type-set-with-rules (cdr tp-lst)
                              term force-flg dwp type-alist1 ancestors ens w
                              ts2
                              (if (and (ts= ts2 ts)
                                       (equal type-alist type-alist1))
                                  ttree
                                  ttree1)
                              pot-lst pt backchain-limit extended-p))))))

;; Historical Comment from Ruben Gamboa:
;; I added an entry for floor1, which is the only primitive
;; non-recognizer function we added for the reals.  [Ruben added entries for
;; some other non-standard primitives too.]

(defun type-set-primitive (term force-flg dwp type-alist ancestors ens w ttree0
                           pot-lst pt backchain-limit)

; Note that we call our initial ttree ttree0 and we extend it below to ttree as
; we get the types of the necessary arguments.  This function should handle
; every non-recognizer function handled in *primitive-formals-and-guards*,
; ev-fncall, and cons-term1, though like cons-term1, we also handle NOT.
; Exception:  Since code-char is so simple type-theoretically, we handle its
; type set computation with rule code-char-type in axioms.lisp.  It is
; perfectly acceptable to handle function symbols here that are not handled by
; the functions above.  For example, we compute a type-set for length in a
; special manner below, but cons-term1 and the others do not know about
; length.

  (case (ffn-symb term)
        (cons
         (mv-let (ts2 ttree)
                 (type-set-rec (fargn term 2)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-cons ts2 ttree ttree0)))
        (equal
         (cond ((equal (fargn term 1) (fargn term 2))
                (mv *ts-t* ttree0))
               (t (mv-let (ts1 ttree)
                          (type-set-rec (fargn term 1)
                                        force-flg
                                        dwp
                                        type-alist
                                        ancestors
                                        ens
                                        w
                                        ttree0
                                        pot-lst pt backchain-limit)
                          (mv-let (ts2 ttree)
                                  (type-set-rec (fargn term 2)
                                                force-flg
                                                dwp
                                                type-alist
                                                ancestors
                                                ens
                                                w
                                                ttree
                                                pot-lst pt backchain-limit)
                                  (type-set-equal ts1 ts2 ttree ttree0))))))
        (unary--
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-unary-- ts1 ttree ttree0)))
        (unary-/
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-unary-/ ts1 ttree ttree0)))
        #+:non-standard-analysis
        (floor1
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-floor1 ts1 ttree ttree0)))
        (denominator
         (mv-let (ts1 ttree)
           (type-set-rec (fargn term 1)
                         force-flg
                         dwp
                         type-alist
                         ancestors
                         ens
                         w
                         ttree0
                         pot-lst pt backchain-limit)
           (type-set-denominator ts1 ttree ttree0)))
        (numerator
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-numerator ts1 ttree ttree0)))
        #+:non-standard-analysis
        (standardp
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-standardp ts1 ttree ttree0)))
        #+:non-standard-analysis
        (standard-part
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-standard-part ts1 ttree ttree0)))
        #+:non-standard-analysis
        (i-large-integer
         (mv *ts-integer>1* (puffert ttree0)))
        (car
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-car ts1 ttree ttree0)))
        (cdr
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-cdr ts1 ttree ttree0)))
        (symbol-name
         (mv *ts-string* (puffert ttree0)))
        (symbol-package-name
         (mv *ts-string* (puffert ttree0)))
        (intern-in-package-of-symbol
         (mv-let (ts1 ttree1)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (mv-let (ts2 ttree2)
                         (type-set-rec (fargn term 2)
                                       force-flg
                                       dwp
                                       type-alist
                                       ancestors
                                       ens
                                       w
                                       ttree0
                                       pot-lst pt backchain-limit)

; Note that ttree1 and ttree2 both have ttree0 in them, but ttree2 does not
; have ttree1 in it!
                         (type-set-intern-in-package-of-symbol ts1 ts2
                                                               ttree1 ttree2
                                                               ttree0))))
        (pkg-witness
         (mv *ts-symbol* (puffert ttree0)))
        (coerce
         (mv-let (ts1 ttree1)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (mv-let (ts2 ttree2)
                         (type-set-rec (fargn term 2)
                                       force-flg
                                       dwp
                                       type-alist
                                       ancestors
                                       ens
                                       w
                                       ttree0
                                       pot-lst pt backchain-limit)

; Note that ttree1 and ttree2 both have ttree0 in them, but ttree2 does not
; have ttree1 in it!
                         (type-set-coerce term ts1 ts2 ttree1 ttree2 ttree0))))
        (length
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-length ts1 ttree ttree0)))
        (binary-+
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (mv-let (ts2 ttree)
                         (type-set-rec (fargn term 2)
                                       force-flg
                                       dwp
                                       type-alist
                                       ancestors
                                       ens
                                       w
                                       ttree
                                       pot-lst pt backchain-limit)
                         (type-set-binary-+ term ts1 ts2 ttree ttree0))))
        (binary-*
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (mv-let (ts2 ttree)
                         (type-set-rec (fargn term 2)
                                       force-flg
                                       dwp
                                       type-alist
                                       ancestors
                                       ens
                                       w
                                       ttree
                                       pot-lst pt backchain-limit)
                         (type-set-binary-* ts1 ts2 ttree ttree0))))
        (<
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (mv-let (ts2 ttree)
                         (type-set-rec (fargn term 2)
                                       force-flg
                                       dwp
                                       type-alist
                                       ancestors
                                       ens
                                       w
                                       ttree
                                       pot-lst pt
                                       backchain-limit)
                         (type-set-< (fargn term 1)
                                     (fargn term 2)
                                     ts1 ts2
                                     type-alist ttree ttree0
                                     pot-lst pt))))
        (not
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-not ts1 ttree ttree0)))
        (realpart
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-realpart ts1 ttree ttree0)))
        (imagpart
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-imagpart ts1 ttree ttree0)))
        (complex
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (mv-let (ts2 ttree)
                         (type-set-rec (fargn term 2)
                                       force-flg
                                       dwp
                                       type-alist
                                       ancestors
                                       ens
                                       w
                                       ttree
                                       pot-lst pt backchain-limit)
                         (type-set-complex ts1 ts2 ttree ttree0))))
        (char-code
         (mv-let (ts1 ttree)
                 (type-set-rec (fargn term 1)
                               force-flg
                               dwp
                               type-alist
                               ancestors
                               ens
                               w
                               ttree0
                               pot-lst pt backchain-limit)
                 (type-set-char-code ts1 ttree ttree0)))
        (otherwise (mv *ts-unknown* ttree0))))

; Mini-Essay on Assume-true-false-if and Implies
; or
; How Strengthening One Part of a Theorem Prover Can Weaken the Whole.

; Normally, when ACL2 rewrites one of the branches of an IF expression,
; it ``knows'' the truth or falsity (as appropriate) of the test.  More
; precisely, if x is a term of the form (IF test true-branch false-branch),
; when ACL2 rewrites true-branch, it can determine that test is true by
; type reasoning alone, and when it rewrites false-branch it can determine
; that test is false by type reasoning alone.  This is certainly what one
; would expect.

; However, previously, if test was such that it would print as (AND
; test1 test2) -- so that x would print as (IF (AND test1 test2)
; true-branch false-branch) -- when ACL2 rewrote true-branch it only
; knew that (AND test1 test2) was true --- it did not know that test1
; was true nor that test2 was true, but only that their conjunction
; was true.  There were also other situations in which ACL2's
; reasoning was weak about the test of an IF expression.

; The function assume-true-false-if was written to correct this problem
; but it caused other problems of its own.  This mini-essay records
; one of the difficulties encountered and its solution.

; In initial tests with the new assume-true-false-if, more than three-
; fourths of the community books failed to certify.  Upon
; examination it turned out that ACL2 was throwing away many of the
; :use hints as well as some of the results from generalization
; rules.  Let us look at a particular example (from inequalities.lisp
; in the arithmetic library):

;;; (defthm <-*-right-cancel
;;;   (implies (and (rationalp x)
;;;                 (rationalp y)
;;;                 (rationalp z))
;;;            (iff (< (* x z) (* y z))
;;;                 (cond
;;;                  ((< 0 z)
;;;                   (< x y))
;;;                  ((equal z 0)
;;;                   nil)
;;;                  (t (< y x)))))
;;;   :hints (("Goal" :use
;;;            ((:instance (:theorem
;;;                         (implies (and (rationalp a)
;;;                                       (< 0 a)
;;;                                       (rationalp b)
;;;                                       (< 0 b))
;;;                                  (< 0 (* a b))))
;;;                        (a (abs (- y x)))
;;;                        (b (abs z)))))))

; This yields the subgoal:

;;;  (IMPLIES (IMPLIES (AND (RATIONALP (ABS (+ Y (- X))))
;;;           (< 0 (ABS (+ Y (- X))))
;;;           (RATIONALP (ABS Z))
;;;           (< 0 (ABS Z)))
;;;                    (< 0 (* (ABS (+ Y (- X))) (ABS Z))))
;;;  (IMPLIES (AND (RATIONALP X)
;;;                (RATIONALP Y)
;;;                (RATIONALP Z))
;;;           (IFF (< (* X Z) (* Y Z))
;;;                (COND ((< 0 Z) (< X Y))
;;;                      ((EQUAL Z 0) NIL)
;;;                      (T (< Y X))))))

; Previously, the preprocess-clause ledge of the waterfall would
; see this as

;;;   ((NOT (IMPLIES (IF (RATIONALP (ABS (BINARY-+ Y (UNARY-- X))))
;;;                      (IF (< '0 (ABS (BINARY-+ Y (UNARY-- X))))
;;;                          (IF (RATIONALP (ABS Z))
;;;                              (< '0 (ABS Z))
;;;                              'NIL)
;;;                          'NIL)
;;;                      'NIL)
;;;                (< '0
;;;                   (BINARY-* (ABS (BINARY-+ Y (UNARY-- X)))
;;;                             (ABS Z)))))
;;;  (IMPLIES (IF (RATIONALP X)
;;;               (IF (RATIONALP Y) (RATIONALP Z) 'NIL)
;;;               'NIL)
;;;           (IFF (< (BINARY-* X Z) (BINARY-* Y Z))
;;;                (IF (< '0 Z)
;;;                    (< X Y)
;;;                    (IF (EQUAL Z '0) 'NIL (< Y X))))))

; and return

;;;  (((NOT (IF (IF (RATIONALP (ABS (BINARY-+ Y (UNARY-- X))))
;;;                 (IF (< '0 (ABS (BINARY-+ Y (UNARY-- X))))
;;;                     (IF (RATIONALP (ABS Z))
;;;                         (< '0 (ABS Z))
;;;                         'NIL)
;;;                     'NIL)
;;;                 'NIL)
;;;                    (IF (< '0
;;;                           (BINARY-* (ABS (BINARY-+ Y (UNARY-- X)))
;;;                                     (ABS Z)))
;;;                        'T
;;;                        'NIL)
;;;                    'T))
;;;           (NOT (RATIONALP X))
;;;           (NOT (RATIONALP Y))
;;;           (NOT (RATIONALP Z))
;;;           (IF (< (BINARY-* X Z) (BINARY-* Y Z))
;;;               (IF (IF (< '0 Z)
;;;                       (< X Y)
;;;                       (IF (EQUAL Z '0) 'NIL (< Y X)))
;;;                   'T
;;;                   'NIL)
;;;               (IF (IF (< '0 Z)
;;;                       (< X Y)
;;;                       (IF (EQUAL Z '0) 'NIL (< Y X)))
;;;                   'NIL
;;;                   'T))))
; Now, under the old regime, when rewrite got hold of the conclusion
; of the :use hint,

; (< '0
;    (BINARY-* (ABS (BINARY-+ Y (UNARY-- X)))
;              (ABS Z)))

; it would would know that X, Y, and Z were rational and that the IF
; expression

; (IF (RATIONALP (ABS (BINARY-+ Y (UNARY-- X))))
;     (IF (< '0 (ABS (BINARY-+ Y (UNARY-- X))))
;         (IF (RATIONALP (ABS Z))
;             (< '0 (ABS Z))
;             'NIL)
;         'NIL)
;     'NIL)

; was true.  But it would not know, for instance, that
; (< '0 (ABS (BINARY-+ Y (UNARY-- X)))) was true.

; With the introduction of assume-true-false-if, however, ACL2 would
; know that each element of the conjunction represented by the IF
; expression was true, and so would be able to determine that the
; conclusion of the :use hint was true by type-reasoning alone (since
; the original :theorem was so proved).  Thus, the whole hint rewrites
; to true and is removed.  Bummer.

; Previously, the conclusion of a :use hint or of a fact derived from
; a generalization rule would, in affect, be rewritten (the first
; time) under the type-alist of the overall goal to be proved.  We now
; handle IMPLIES differently in order to return to this original
; behavior.

; The basic idea is not to expand IMPLIES except within rewrite where
; we can easily maintain the proper type-alists.  Two simple exceptions
; to this rule are in tautologyp and distribute-first-if.  We expand
; IMPLIES within tautologyp for obvious reasons and within distribute-
; first-if because earlier tests (presumably still valid) showed that
; this was both faster and more fruitful.  Note that this second
; exception implies that an IMPLIES will never show up due to a user
; defined function.

; A slightly more subtle exception is in preprocess-clause where we
; expand an IMPLIES if it is derived from the original theorem to be
; proved.  This is necessary to provide a context for rewrite (See the
; comments in preprocess-clause beginning ``Note: Once upon a time (in
; Version 1.5)'' for more on this.

;; Historical Comment from Ruben Gamboa:
;; In this function, I relaxed the tests for rational to include
;; realp as well.

(defun assume-true-false-if (not-flg x xttree force-flg dwp
                                     type-alist ancestors ens w
                                     pot-lst pt backchain-limit)

; X is an IF-expression we have been asked to assume-true-false.  We
; return the standard tuple through the standard calls to mv-atf.

; The original motivation for this function lay in the fact that, within
; ACL2's logic, conjunctions and disjunctions are encoded as IF
; expressions.  In the simplest (conceptually) case, x is of the form
; (IF a b 'nil) which is the translation of (AND a b).  This function
; then ensures that the truth of both a and b are recorded in the
; true-type-alist returned.  It is, however, written to handle the
; general case.

  (let ((test (fargn x 1))
        (true-branch (fargn x 2))
        (false-branch (fargn x 3)))

; We start by recurring on the test.

    (mv-let (test-mbt test-mbf test-tta test-fta test-ttree)
            (assume-true-false-rec test xttree force-flg
                                   dwp type-alist ancestors ens w
                                   pot-lst pt nil
                                   backchain-limit)

; In the first two branches, we know that test must be true or that test
; must be false.  We recur on the true branch or the false branch
; respectively.  Test-ttree is a (possibly trivial) extension of xttree
; containing any assumptions made when calling assume-true-false on test,
; so we use it on the recursive calls.

            (cond
             (test-mbt
              (mv-let (mbt mbf tta fta ttree)
                      (assume-true-false-rec true-branch test-ttree force-flg
                                             dwp test-tta ancestors ens w
                                             pot-lst pt nil
                                             backchain-limit)
                      (mv-atf not-flg mbt mbf tta fta ttree nil)))
             (test-mbf
              (mv-let (mbt mbf tta fta ttree)
                      (assume-true-false-rec false-branch test-ttree force-flg
                                             dwp test-fta ancestors ens w
                                             pot-lst pt nil
                                             backchain-limit)
                      (mv-atf not-flg mbt mbf tta fta ttree nil)))

             (t

; We do not know whether test must be true or test must be false.  We
; recur on both true-branch and false-branch, using test-tta and test-fta
; respectively.  These two type-alists are proper extensions of type-alist
; which record the assumed type of test.  We use xttree since test-ttree
; is nil.

              (mv-let
               (tb-mbt tb-mbf tb-tta tb-fta tb-ttree)
               (assume-true-false-rec true-branch xttree force-flg
                                      dwp test-tta ancestors ens w
                                      pot-lst pt nil backchain-limit)
               (mv-let
                (fb-mbt fb-mbf fb-tta fb-fta fb-ttree)
                (assume-true-false-rec false-branch xttree force-flg
                                       dwp test-fta ancestors ens w
                                       pot-lst pt nil backchain-limit)
                (cond

                 ((and tb-mbf fb-mbf)

; Since both branches must be false, x must be false.  It is probably
; not very useful, but we record this fact in the returned type-alist.
; Tb-ttree and fb-ttree record any assumptions made, so we must record
; them in the type-alist also.

                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts= x-ts *ts-nil*)
                                 (mv-atf not-flg nil t
                                         nil type-alist
                                         xttree x-ts-ttree))

; Here, we formerly checked (ts-disjointp x-ts *ts-nil*) and caused a hard
; error if that was true, suggesting to contact the implementors with an
; example.  However, the example below shows that this case can occur.  We are
; in an inconsistent context, and we simply ignore the problematic entry
; accessed by look-in-type-alist, starting after Version_8.0.

; We have provoked this case, where (ts-disjointp x-ts *ts-nil*), with the
; following example.  It is derived from an example sent to us by Dave Greve,
; and the defun below is essentially his, included with his permission.
; Below we say more about invoking the error in Version_8.0.

;   (include-book "arithmetic-5/top" :dir :system)
;
;   (defun find-next (var best list)
;     (if (not (consp list))
;         best
;       (let ((new (car list)))
;         (let ((best (if (< best var)
;                         best (if (< new var) new var))))
;           (if (and (< new var) (<= best new))
;               (find-next var new (cdr list))
;             (find-next var best (cdr list)))))))
;
;   (thm (implies (and (rationalp (find-next var list1 list2))
;                      (<= var 0))
;                 xxx))

; To get a sense of what went wrong, you can do the following in Version 8.0
; before evaluating the forms (or at least, the THM) above.

;   (value :q)
;   (setq *hard-error-is-error* t)
;   (set-debugger-enable t)
;   (lp)

; When in the CCL debugger, submit these expressions.

;   (:form 2)
;   (butlast * 5)

; This provides a call of assume-true-false-if that leads to the error.  By
; eliminating some distracting entries from the type-alist, we obtain this
; call, which leads to the error even when you start up ACL2 and provide no
; initial events.

;   (assume-true-false-if
;    nil
;    '(if (acl2-numberp var)
;         (if (acl2-numberp (car list2))
;             (< (car list2) var)
;           'nil)
;       (if (acl2-numberp (car list2))
;           (< (car list2) '0)
;         'nil))
;    nil nil nil
;    '(((car list2) -128)
;      ((if (acl2-numberp var)
;           (if (acl2-numberp (car list2))
;               (< (car list2) var)
;             'nil)
;         (if (acl2-numberp (car list2))
;             (< (car list2) '0)
;           'nil))
;       -129))
;    nil (ens state) (w state) nil nil nil)

                                (t
                                 (mv-atf not-flg nil t
                                         nil
                                         (extend-type-alist-simple
                                          x *ts-nil*
                                          (cons-tag-trees tb-ttree fb-ttree)
                                          type-alist)

; Observe that we let mv-atf cons these two ttrees together.  We do this
; repeatedly in the calls of mv-atf below.

                                         tb-ttree fb-ttree)))))

                 ((and tb-mbt fb-mbt)

; Since both branches must be true, x must be true (non-nil).

                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts-disjointp x-ts *ts-nil*)
                                 (mv-atf not-flg t nil
                                         type-alist nil
                                         xttree x-ts-ttree))

; Here, we formerly checked (ts= x-ts *ts-nil*) and caused a hard error if that
; was true, suggesting to contact the implementors with an example.  However,
; we have seen a case like this arise; see the example above, under the
; preceding call of look-in-type-alist.  We believe that this odd case
; indicates an inconsistent context, so we simply ignore the problematic entry
; accessed by look-in-type-alist.

                                (t
                                 (mv-atf not-flg t nil
                                         (extend-type-alist-simple
                                          x

; The ts= test above ensures that this intersection is not the empty type.
; We also know that x-ts is not equal to (ts-intersection x-ts *ts-non-nil*)
; because of the (not (ts-intersectp x-ts *ts-nil*)) test above.

                                          (ts-intersection x-ts *ts-non-nil*)
                                          (cons-tag-trees x-ts-ttree
                                                          (cons-tag-trees
                                                           tb-ttree
                                                           fb-ttree))
                                          type-alist)
                                         nil

; We do not need to use x-ts-ttree here, because x-ts is only being
; used to (possibly) tighten up the type of x stored in the type-alist.
; It is not being used in the determination that x must-be-true.

                                         tb-ttree fb-ttree)))))

                 ((and tb-mbt fb-mbf)

; Since the true branch must be true and the false branch must be false
; we know that
; a) The true type-alist we return should include that test and the
;    true branch are both true.
; b) The false type-alist we return should include that test and the
;    false branch are both false.
; Note that tb-tta and fb-fta contain exactly this information.
; However, we must infect any new entries with the ttrees which record
; any assumptions made in deriving these conclusions.

                  (mv-atf not-flg nil nil
                          (infect-new-type-alist-entries
                           tb-tta type-alist
                           (cons-tag-trees tb-ttree fb-ttree))
                          (infect-new-type-alist-entries
                           fb-fta type-alist
                           (cons-tag-trees tb-ttree fb-ttree))
                          nil nil))

                 ((and tb-mbf fb-mbt)
                  (mv-atf not-flg nil nil
                          (infect-new-type-alist-entries
                           fb-tta type-alist
                           (cons-tag-trees tb-ttree fb-ttree))
                          (infect-new-type-alist-entries
                           tb-fta type-alist
                           (cons-tag-trees tb-ttree fb-ttree))
                          nil nil))

                 (tb-mbt

; Since the true-branch must be true, the only way we can get a
; false-type-alist is if the test is false and the false-branch is false.
; The false-branch false-type-alist contains this information.
; We know little about a true-type-alist however.

                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts= x-ts *ts-nil*)
                                 (mv-atf not-flg nil t
                                         nil
                                         (infect-new-type-alist-entries
                                          fb-fta type-alist
                                          tb-ttree)
                                         xttree x-ts-ttree))
                                ((ts-disjointp x-ts *ts-nil*)
                                 (mv-atf not-flg t nil
                                         type-alist nil
                                         xttree x-ts-ttree))
                                (t
                                 (mv-atf not-flg nil nil
                                         (extend-type-alist-simple
                                          x
                                          (ts-intersection x-ts *ts-non-nil*)
                                          (cons-tag-trees x-ts-ttree xttree)
                                          type-alist)
                                         (infect-new-type-alist-entries
                                          fb-fta type-alist
                                          tb-ttree)
                                         nil nil)))))

                 (tb-mbf
                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts= x-ts *ts-nil*)
                                 (mv-atf not-flg nil t
                                         nil type-alist
                                         xttree x-ts-ttree))
                                ((ts-disjointp x-ts *ts-nil*)
                                 (mv-atf not-flg t nil
                                         (infect-new-type-alist-entries
                                          fb-tta type-alist
                                          tb-ttree)
                                         nil
                                         xttree x-ts-ttree))
                                (t
                                 (mv-atf not-flg nil nil
                                         (infect-new-type-alist-entries
                                          fb-tta type-alist
                                          tb-ttree)
                                         (extend-type-alist-simple
                                          x *ts-nil* xttree type-alist)
                                         nil nil)))))

                 (fb-mbt
                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts= x-ts *ts-nil*)
                                 (mv-atf not-flg nil t
                                         nil
                                         (infect-new-type-alist-entries
                                          tb-fta type-alist
                                          fb-ttree)
                                         xttree x-ts-ttree))
                                ((ts-disjointp x-ts *ts-nil*)
                                 (mv-atf not-flg t nil
                                         type-alist nil
                                         xttree x-ts-ttree))
                                (t
                                 (mv-atf not-flg nil nil
                                         (extend-type-alist-simple
                                          x
                                          (ts-intersection x-ts *ts-non-nil*)
                                          (cons-tag-trees x-ts-ttree xttree)
                                          type-alist)
                                         (infect-new-type-alist-entries
                                          tb-fta type-alist
                                          fb-ttree)
                                         nil nil)))))

                 (fb-mbf
                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts= x-ts *ts-nil*)
                                 (mv-atf not-flg nil t
                                         nil type-alist
                                         xttree x-ts-ttree))
                                ((ts-disjointp x-ts *ts-nil*)
                                 (mv-atf not-flg t nil
                                         (infect-new-type-alist-entries
                                          tb-tta type-alist
                                          fb-ttree)
                                         nil
                                         xttree x-ts-ttree))
                                (t
                                 (mv-atf not-flg nil nil
                                         (infect-new-type-alist-entries
                                          tb-tta type-alist
                                          fb-ttree)
                                         (extend-type-alist-simple
                                          x *ts-nil* xttree type-alist)
                                         nil nil)))))
                 (t
                  (mv-let (x-ts x-ts-ttree)
                          (look-in-type-alist x type-alist w)
                          (cond ((ts= x-ts *ts-nil*)
                                 (mv-atf not-flg nil t
                                         nil type-alist
                                         xttree x-ts-ttree))
                                ((ts-disjointp x-ts *ts-nil*)
                                 (mv-atf not-flg t nil
                                         type-alist nil
                                         xttree x-ts-ttree))
                                (t
                                 (mv-atf not-flg nil nil
                                         (extend-type-alist-simple
                                          x
                                          (ts-intersection x-ts *ts-non-nil*)
                                          (cons-tag-trees x-ts-ttree xttree)
                                          type-alist)
                                         (extend-type-alist-simple
                                          x *ts-nil* xttree type-alist)
                                         nil nil)))))))))))))

(defun assume-true-false-rec (x xttree force-flg dwp type-alist ancestors ens w
                                pot-lst pt ignore0 backchain-limit)

; We assume x both true and false, extending type-alist as appropriate.
; Xttree is the ttree with which we are to tag all the entries added to
; type-alist when assuming x.  Generally speaking, xttree will contain
; a 'PT tag whose value is a parent tree for x.

; We return five values.
; must-be-true     - t iff x is definitely true under type-alist and w.
; must-be-false    - t iff x is definitely false under type-alist and w.
; true-type-alist  - an extension of type-alist encoding the assumption
;                    that x is true; valid only if not must-be-false.
; false-type-alist - an extension of type-alist encoding the assumption
;                    that x is false; valid only if not must-be-true.
; ttree            - a ttree recording all of the facts used to establish
;                    x definitely true or definitely false.  This result is
;                    nil if must-be-true and must-be-false are both nil.
;                    Ttree will always include xttree when ttree is non-nil.
;                    That is, if we decide the question of x's truth or
;                    falsity we report a dependency on xttree just as we
;                    would if we had assumed it and then asked about it.

; Input ignore0 is generally nil, but can be :tta or :fta if we will ignore the
; resulting true-type-alist or false-type-alist, respectively.  The following
; example, essentially from Dave Greve, shows a roughly 4X speedup using these
; flags, and saves nearly a billion bytes for cons cells (!), in an Allegro
; Common Lisp run.


;;; (progn
;;;   (defstub kstate-p (k) nil)
;;;   (defstub aamp-st-p (st) nil)
;;;   (defstub kstate-u (k) nil)
;;;   (defstub kstate-k (k) nil)
;;;   (defstub pred (k st) nil)
;;;
;;;   (defaxiom rule
;;;     (implies
;;;      (equal (kstate-k k) 0)
;;;      (equal (pred k st) 1))))
;;;
;;; (defun gen-forms (n acc)
;;;   (declare (xargs :mode :program))
;;;   (if (zp n)
;;;       acc
;;;     (gen-forms (1- n)
;;;                (cons `(NOT (EQUAL (KSTATE-U K) ,n))
;;;                      acc))))
;;;
;;; (defmacro mac ()
;;;   `(AND (KSTATE-P K)
;;;         (AAMP-ST-P ST)
;;;         ,@(gen-forms 560 nil)
;;;         (NOT (EQUAL (KSTATE-U K) -1))
;;;         (EQUAL (KSTATE-K K) 0)))
;;;
;;; (time$ ; optional timing from Matt K.
;;;  (thm (IMPLIES (mac)
;;;                (EQUAL (pred k st)
;;;                       1))
;;;       ;; optional from Matt K.:
;;;       :hints (("Goal" :do-not '(preprocess)))))

  (mv-let (xnot-flg x)

; Rockwell Addition:  This is a minor improvement.

; The following is just (strip-not term) except it also recognizes (IF
; x NIL T) as (NOT x).  The former comes up when we expand (ATOM x)
; using its body.

    (cond ((nvariablep x)

; Warning:  Actually x might be a quoted constant here.  But we ask
; if the ffn-symb is either NOT or IF and if it is QUOTE we will
; fail those tests anyway.  So this is a delicate but legitimate
; violation of our term abstract data type.  Of course, we could use ffn-symb-p
; here, but then we could be testing nvariablep twice.

           (cond ((eq (ffn-symb x) 'NOT)
                  (mv t (fargn x 1)))
                 ((and (eq (ffn-symb x) 'IF)
                       (equal (fargn x 2) *nil*)
                       (equal (fargn x 3) *t*))
                  (mv t (fargn x 1)))
                 (t (mv nil x))))
          (t (mv nil x)))

    (cond
     ((variablep x)
      (assume-true-false1
       xnot-flg x xttree force-flg dwp type-alist ancestors ens w
       pot-lst pt backchain-limit))
     ((fquotep x)
      (if (equal x *nil*)
          (mv-atf xnot-flg nil t nil type-alist nil xttree)
        (mv-atf xnot-flg t nil type-alist nil nil xttree)))
     ((flambda-applicationp x)
      (assume-true-false1 xnot-flg x xttree
                          force-flg dwp type-alist ancestors ens w
                          pot-lst pt backchain-limit))
     (t
      (mv-let (var strongp true-ts false-ts rune[s])
        (recognizer-expr-p x ens w)
        (let ((ignore (adjust-ignore-for-atf xnot-flg ignore0)))
          (cond
           (var

; Before v2-8, we did not check whether x is already explicitly true or false
; in the given type-alist.  Here is an example of what can go wrong,
; contributed (in essence) by Eric Smith.

;;;  (defund mod4 (n)
;;;    (if (not (integerp n)) 0 (mod n 4)))
;;;
;;;  (defun even-aux (x)
;;;    (if (zp x)
;;;        t
;;;        (if (eql 1 x) nil (even-aux (+ -2 x)))))
;;;
;;;  (defund even (x)
;;;    (if (not (integerp x))
;;;        nil
;;;        (if (< x 0)
;;;            (even-aux (- x))
;;;            (even-aux x))))
;;;
;;;  (skip-proofs
;;;   (defthm mod4-is-0-fw-to-even
;;;     (implies (and (equal 0 (mod4 n))
;;;                   (integerp n))
;;;              (even n))
;;;     :rule-classes (:forward-chaining)))
;;;
;;;  ; succeeds
;;;  (thm (implies (and (equal 0 (mod4 n))
;;;                     (integerp n))
;;;                (even n)))
;;;
;;;  (skip-proofs
;;;   (defthm even-means-integerp
;;;     (implies (even x) (integerp x))
;;;     :rule-classes
;;;     (:compound-recognizer)))
;;;
;;;  ; fails (but succeeds after the change for v2-8, where we do the
;;;  ;        assoc-type-alist below)
;;;  (thm (implies (and (equal 0 (mod4 n))
;;;                     (integerp n))
;;;                (even n)))

            (mv-let
              (ts ttree)
              (cond (strongp

; We do not put expect to put calls of strong recognizers in the type-alist.
; See the discussion of strongp above the calls of
; extend-with-proper/improper-cons-ts-tuple below.

                     (mv nil nil))
                    (t (assoc-type-alist x type-alist w)))
              (cond
               ((and ts (ts= ts *ts-nil*))
                (mv-atf xnot-flg nil t nil type-alist ttree xttree))
               ((and ts (ts-disjointp ts *ts-nil*))
                (mv-atf xnot-flg t nil type-alist nil ttree xttree))
               (t
                (mv-let (ts0 arg)
                  (if (eq var :one)
                      (strengthen-recog-call x)
                    (mv nil var))
                  (mv-let
                    (ts ttree)
                    (type-set-rec arg force-flg
                                  dwp
                                  type-alist ancestors ens w nil
                                  pot-lst pt backchain-limit)
                    (let ((t-int (ts-intersection ts
                                                  (if ts0
                                                      (ts-union ts0 true-ts)
                                                    true-ts)))
                          (f-int (ts-intersection ts false-ts)))
                      (cond
                       ((ts= t-int *ts-empty*)
                        (cond
                         ((ts= f-int *ts-empty*)

; We are in a contradictory context, which can happen "in the wild".  For
; example, if we put the following trace on type-set-rec and then run the first
; event from :mini-proveall, as shown, we will see call of type-set-rec similar
; to the one below, that gives result *ts-empty*.

;   (trace$ (type-set-rec
;            :cond
;            (and (equal x '(cdr x))
;                 (subsetp-equal '((x 1024) ((cdr x) -1153)) type-alist))))

;   (thm (implies (and (true-listp x) (true-listp y))
;                      (equal (revappend (append x y) z)
;                             (revappend y (revappend x z)))))

;   (type-set-rec '(cdr x) nil t
;                 '((x 1024)
;                   ((cdr x) -1153))
;                 nil (ens state) (w state) nil nil nil nil)

; Empty type-sets also arise when ACL2 is inferring type-prescriptions for
; functions empty type-sets.  In this case, when both t-int and f-int are
; *ts-empty*, we set both must-be-true and must-be-false to t.  It probably
; doesn't matter logically what we return for the type-alists, but we return
; type-alist in case it's useful to the caller (see for example the handling of
; assume-true-false calls in rewrite-if).

                          (mv-atf xnot-flg t t type-alist type-alist
                                  (push-lemma[s] var
                                                 rune[s]
                                                 (if ts0 (puffert ttree) ttree))
                                  xttree))
                         (t (mv-atf xnot-flg nil t nil type-alist
                                    (push-lemma[s]
                                     var
                                     rune[s]
                                     (if ts0 (puffert ttree) ttree))
                                    xttree))))
                       ((ts= f-int *ts-empty*)
                        (mv-atf xnot-flg t nil type-alist nil
                                (push-lemma[s] var rune[s] ttree)
                                xttree))
                       (t

; At this point we know that we can't determine whether (recog arg) is
; true or false.  We therefore will be returning two type-alists which
; restrict arg's type according to the two intersections computed
; above.  Both of these restrictions will depend upon rune (be-
; cause we used the rule to determine the types recognized by recog),
; ttree (because that was the previously known type of arg and was
; involved in the intersections), and xttree (because by contract we
; are obliged to make all new tuples depend on it).  So we construct
; shared-ttree below so we don't have to recreate this ttree twice (once
; for the tta and once for the fta).

                        (let ((shared-ttree
                               (push-lemma[s]
                                var
                                rune[s]
                                (if ts0
                                    (puffert (cons-tag-trees ttree xttree))
                                  (cons-tag-trees ttree xttree)))))

; The two calls of extend-with-proper/improper-cons-ts-tuple below can be
; thought of as simply extending a type-alist with (list* arg int
; shared-ttree).  They actually do some reasoning about true-lists but the
; effect of adding the tuples they produce to tta and fta is just to restrict
; the type of arg.  Now if recog is strongp, then the truth and falsity of
; (recog arg) is determined by the appropriate restriction on the type of arg
; and there is no need to add anything else to type-alist to form tta and fta.
; But if recog is not strongp, we need to record the additional assumptions
; that (recog arg) is true or false, appropriately.  That is why there are
; ``if'' expressions in the calls of extend-with-proper/improper-cons-ts-tuple
; below: it determines whether we add the arg restriction to type-alist itself
; or to an extension of type-alist that restricts (recog arg) appropriately.
; The assumption that (recog arg) is true depends both on xttree (by contract)
; and the rune, since we are exploiting the fact that recog is Boolean.  The
; assumption that (recog arg) is false only depends on xttree.

                          (mv-atf xnot-flg nil nil
                                  (and (not (eq ignore :tta))
                                       (extend-with-proper/improper-cons-ts-tuple
                                        arg t-int shared-ttree force-flg
                                        dwp type-alist ancestors ens
                                        (if strongp
                                            type-alist
                                          (extend-type-alist-simple
                                           x *ts-t*
                                           (push-lemma[s] var rune[s] xttree)
                                           type-alist))
                                        w
                                        pot-lst pt backchain-limit))
                                  (and (not (eq ignore :fta))
                                       (extend-with-proper/improper-cons-ts-tuple
                                        arg f-int shared-ttree force-flg
                                        dwp type-alist ancestors ens
                                        (if strongp
                                            type-alist
                                          (extend-type-alist-simple
                                           x *ts-nil* xttree type-alist))
                                        w
                                        pot-lst pt backchain-limit))
                                  nil nil)))))))))))
           ((member-eq (ffn-symb x)
                       *expandable-boot-strap-non-rec-fns*)

; Why do we expand these functions?  The original motivating example involved
; guards and stemmed from the pre-1.8 days.  However, here is a distillation of
; that example for Version 1.8 that illustrates that expansion may help.
; The bottom line in the example is that assuming (= x 0) false is less
; helpful than assuming (equal x 0) false.

; What is the type of the following expression?  One way to experiment is
; to define (foo n) to be the expression below.
; (if (and (integerp n) (>= n 0))
;     (if (equal n 0)
;         t
;         (if (> n 0) t nil))
;   t)
; The answer is that it always returns t.  That is because if we know n is
; in *ts-non-negative-integer* and then we learn that (equal n 0) is nil,
; then we know that n is in *ts-positive-integer* and so (> n 0) is true.
; Now what is the type of
; (if (and (integerp n) (>= n 0))
;     (if (= n 0)
;         t
;         (if (> n 0) t nil))
;   t)
; If the (= n 0) is not expanded into an equal, the answer reported is Boolean.
; We do not learn from the falsity of (= n 0) that n is non-0.

            (mv-let
              (mbt mbf tta fta ttree)
              (assume-true-false-rec
               (subcor-var (formals (ffn-symb x) w)
                           (fargs x)
                           (bbody (ffn-symb x)))
               xttree force-flg dwp type-alist ancestors ens w
               pot-lst pt ignore backchain-limit)
              (if xnot-flg
                  (mv mbf mbt fta tta ttree)
                (mv mbt mbf tta fta ttree))))
           ((eq (ffn-symb x) 'equal)
            (let ((arg1 (fargn x 1))
                  (arg2 (fargn x 2)))
              (cond
               ((equal arg1 arg2)
                (mv-atf xnot-flg t nil type-alist nil nil

; We could just as well use (push-lemma '(:executable-counterpart equal)
; xttree) here instead.  But in order to maintain analogy with the general case
; of an equivalence relation, we'll add the fake rune for type-set instead.  As
; noted elsewhere, if we ever give runic names to the theorems establishing
; equivalence-relation-hood and track those names through geneqvs, then we
; ought to push the appropriate rune here, rather than use puffert, which was
; intended for primitives and is thus here somewhat misused unless perhaps
; equiv is 'equal.

                        (puffert xttree)))
               ((and (quotep arg1) (quotep arg2))
                (mv-atf xnot-flg nil t nil type-alist nil
                        (push-lemma '(:executable-counterpart equal) xttree)))
               (t
                (mv-let
                  (occursp1 canonicalp1 arg1-canon ttree1)
                  (canonical-representative 'equal arg1 type-alist)

; Recall from the comment in the definition of canonical-representative that if
; occursp equals nil, then term-canon equals term.  It follows that in the
; present context, where arg1 and arg2 are distinct and are not both quoteps,
; the next two COND tests remain logically the same if we remove the occursp1
; conjuncts.  But we have put in the occursp1 conjuncts just in order to gain,
; we think, just a bit of efficiency.  They could of course be omitted.  We
; take a similar step a bit further below, with occursp2.

                  (cond
                   ((and occursp1 (equal arg1-canon arg2))
                    (mv-atf xnot-flg t nil type-alist nil
                            nil

; Since we know that mv-atf will make the call of cons-tag-trees, we go ahead
; and do it now so that puffert can be called on the outside, thus perhaps
; eliminating an unnecessary cons.  We pull such a stunt a number of other
; times in calls of mv-atf.

                            (puffert (cons-tag-trees ttree1 xttree))))
                   ((and occursp1 (quotep arg1-canon) (quotep arg2))
                    (mv-atf xnot-flg nil t nil type-alist
                            nil
                            (push-lemma
                             '(:executable-counterpart equal)
                             (puffert (cons-tag-trees ttree1 xttree)))))
                   (t
                    (mv-let
                      (occursp2 canonicalp2 arg2-canon ttree2)
                      (canonical-representative 'equal arg2 type-alist)
                      (cond
                       ((and occursp2 (equal arg1-canon arg2-canon))
                        (mv-atf xnot-flg t nil type-alist nil
                                nil
                                (puffert
                                 (cons-tag-trees
                                  xttree
                                  (cons-tag-trees ttree1 ttree2)))))
                       ((and occursp2 (quotep arg1-canon) (quotep arg2-canon))
                        (mv-atf xnot-flg nil t nil type-alist
                                nil
                                (push-lemma
                                 '(:executable-counterpart equal)
                                 (puffert (cons-tag-trees
                                           xttree
                                           (cons-tag-trees ttree1 ttree2))))))
                       (t
                        (let ((temp-temp
                               (assoc-equiv 'equal arg1-canon arg2-canon
                                            type-alist)))
                          (cond
                           (temp-temp
                            (cond ((ts= (cadr temp-temp) *ts-t*)

; Arg1-canon and arg2-canon are both supposed to be canonical, so this case
; can't happen!  It would be sound to return:

;                                 (mv-atf xnot-flg t nil type-alist nil
;                                         nil
;                                         (puffert
;                                          (cons-tag-trees
;                                           (cddr temp-temp)
;                                           (cons-tag-trees
;                                            ttree1
;                                            (cons-tag-trees ttree2 xttree)))))

; here, but let's see if we really understand what is going on!

                                   (mv-atf (er hard 'assume-true-false
                                               "Please send the authors of ACL2 a ~
                                           replayable transcript of this ~
                                           problem if possible, so that they ~
                                           can see what went wrong in the ~
                                           function assume-true-false.  The ~
                                           offending call was ~x0.  The ~
                                           surprising type-set arose from a ~
                                           call of ~x1."
                                               (list 'assume-true-false
                                                     (kwote x) '<xttree>
                                                     force-flg (kwote type-alist)
                                                     '<ens> '<w>)
                                               (list 'assoc-equiv
                                                     ''equal
                                                     (kwote arg1-canon)
                                                     (kwote arg2-canon)
                                                     '<same_type-alist>))
                                           nil nil nil nil nil nil))
                                  ((ts= (cadr temp-temp) *ts-nil*)
                                   (mv-atf xnot-flg nil t nil type-alist
                                           nil
                                           (if (and canonicalp1 canonicalp2)

; ... then ttree1 and ttree2 are nil (see comment in canonical-representative),
; and also there's no reason to puffert

                                               (cons-tag-trees (cddr temp-temp)
                                                               xttree)
                                             (puffert
                                              (cons-tag-trees
                                               (cddr temp-temp)
                                               (cons-tag-trees
                                                ttree1
                                                (cons-tag-trees ttree2 xttree)))))))
                                  (t
                                   (let ((erp (assume-true-false-error
                                               type-alist x (cadr temp-temp))))
                                     (mv erp nil nil nil nil)))))
                           (t
                            (mv-let
                              (ts1 ttree)
                              (type-set-rec arg1 force-flg
                                            dwp
                                            type-alist ancestors ens w
                                            nil
                                            pot-lst pt backchain-limit)
                              (mv-let
                                (ts2 ttree)
                                (type-set-rec arg2 force-flg
                                              dwp
                                              type-alist ancestors ens w
                                              ttree
                                              pot-lst pt backchain-limit)

; Observe that ttree records the dependencies of both args.

                                (let ((int (ts-intersection ts1 ts2)))
                                  (cond
                                   ((ts= int *ts-empty*)
                                    (mv-atf xnot-flg nil t nil type-alist
                                            nil
                                            (puffert
                                             (cons-tag-trees ttree xttree))))
                                   ((and (ts= ts1 ts2)
                                         (member ts1 *singleton-type-sets*))
                                    (mv-atf xnot-flg t nil type-alist nil
                                            nil
                                            (puffert
                                             (cons-tag-trees ttree xttree))))
                                   (t
                                    (let* ((swap-flg
                                            (term-order arg1-canon arg2-canon))
                                           (shared-ttree-tta-p

; This is the condition that must hold for shared-ttree to be used for a
; true-type-alist.

                                            (and (not (eq ignore :tta))
                                                 (or (not (ts= ts1 int))
                                                     (not (ts= ts2 int)))))
                                           (shared-ttree

; We could just use (cons-tag-trees ttree xttree) here, but let's save a cons
; if we don't need that tag-tree.

                                            (cond
                                             (shared-ttree-tta-p
                                              (cons-tag-trees ttree xttree))
                                             (t nil)))
                                           (xttree+
                                            (if (and canonicalp1 canonicalp2)

; ... then ttree1 and ttree2 are nil (see comment in canonical-representative),
; and also there's no reason to puffert

                                                xttree
                                              (puffert
                                               (cons-tag-trees
                                                ttree1
                                                (cons-tag-trees ttree2 xttree)))))
                                           (true-type-alist1
                                            (and (not (eq ignore :tta))
                                                 (extend-type-alist1
                                                  'equal occursp1 occursp2
                                                  (and canonicalp1 canonicalp2)
                                                  arg1-canon arg2-canon swap-flg x
                                                  *ts-t* xttree+ type-alist)))
                                           (true-type-alist2
                                            (and (not (eq ignore :tta))
                                                 (cond
                                                  ((ts= ts1 int)
                                                   true-type-alist1)
                                                  (t (extend-with-proper/improper-cons-ts-tuple
                                                      arg1 int shared-ttree
                                                      force-flg dwp type-alist
                                                      ancestors ens
                                                      true-type-alist1 w
                                                      pot-lst pt backchain-limit)))))
                                           (true-type-alist3
                                            (and (not (eq ignore :tta))
                                                 (cond
                                                  ((ts= ts2 int)
                                                   true-type-alist2)
                                                  (t (extend-with-proper/improper-cons-ts-tuple
                                                      arg2 int shared-ttree
                                                      force-flg dwp type-alist
                                                      ancestors ens
                                                      true-type-alist2 w
                                                      pot-lst pt backchain-limit)))))
                                           (false-type-alist1
                                            (and (not (eq ignore :fta))
                                                 (extend-type-alist1
                                                  'equal occursp1 occursp2
                                                  (and canonicalp1 canonicalp2)
                                                  arg1-canon arg2-canon swap-flg x
                                                  *ts-nil* xttree+ type-alist)))
                                           (false-type-alist2
                                            (and (not (eq ignore :fta))
                                                 (cond

; Essay on Strong Handling of *ts-one*

; We are considering a type-alist extension based on (not (equal TM C)) where
; the type-set of C is in *singleton-type-sets*.  The basic idea is to assign a
; type-set to TM by removing the type-set bit for C from what would otherwise
; be the type-set of TM.  In April 2016 we extended the singleton type-sets
; to include *ts-one*.  The question arose: Do we really want to give this
; special treatment to *ts-one*?  Let us call that the "strong handling of
; *ts-one*".

; We considered avoiding such strong handling of *ts-one*, thus saving us from
; numerous regression failures.  For example, consider the lemma
; explode-nonnegative-integer-of-positive-is-not-zero-list in community book
; books/std/io/base.lisp.  If the tests below are simply (member ts2
; *singleton-type-sets*) and (member ts1 *singleton-type-sets*), then that
; proof fails.  However, the proof then once again succeeds if first we modify
; linearize1 so that its type-set calls are made with dwp = t.  That change
; seems potentially expensive, and perhaps could cause many existing books
; (some outside the community books) to fail.  We believe that the reason dwp =
; t is necessary in this example, assuming strong handling of *ts-one*, is that
; assume-true-false-rec produces a false-type-alist by assigning TM to a
; type-set TS with *ts-one* removed, where TM otherwise is not assigned in the
; false-type-alist.  Thus, linearize1 finds the type-set TS for TM, and with
; dwp = nil it fails to find a stronger type that it would have found if TM had
; not been assigned on that type-alist.

; We therefore tried to avoid all strong handling of *ts-one*.  Unfortunately,
; as Jared Davis pointed out, the rule bitp-compound-recognizer then had a weak
; type-set: specifically, the :false-ts for the corresponding recognizer-tuple
; was (ts-complement *ts-zero*) instead of (ts-complement *ts-bit*).

; Our solution attempts to address both of these cases.  We allow strong
; handling of *ts-one* when TM is a variable, which allows the rule
; bitp-compound-recognizer to be given the desired :false-ts.  Note that if TM
; is a variable then the above discussion about dwp = t is probably much less
; relevant, since no type-prescription rule will apply to TM.  However, even if
; TM is not a variable, we provide strong handling of *ts-one* when TM is
; already on the false-type-alist that is to be extended, since in that case,
; the scenario about involving dwp would already find TM on the type-alist, so
; we might as well strengthen the corresponding type by removing the bit for
; *ts-one*.

; Keep this code in sync with *singleton-type-sets*.

                                                  ((or (ts= ts2 *ts-t*)
                                                       (ts= ts2 *ts-nil*)
                                                       (ts= ts2 *ts-zero*)
                                                       (and (ts= ts2 *ts-one*)
                                                            (or (variablep arg1)
                                                                (assoc-equal arg1
                                                                             type-alist))))
                                                   (extend-with-proper/improper-cons-ts-tuple
                                                    arg1
                                                    (ts-intersection
                                                     ts1
                                                     (ts-complement ts2))
                                                    (if shared-ttree-tta-p

; We use the same shared-ttree that we used in the true-type-alist cases above.

                                                        shared-ttree

; Note that since here we know that ts1 and ts2 overlap but are not equal, they
; cannot both be singleton type-sets.  We take advantage of this observation
; below when apparently building the same shared-ttree twice for the two
; false-type-alist cases (this one for false-type-alist2 and the next, for
; false-type-alist3), which however are actually non-overlapping cases because
; this case implies that ts2 is a singleton and the next implies that ts1 is a
; singleton.
                                                      (cons-tag-trees ttree xttree))
                                                    force-flg dwp type-alist ancestors
                                                    ens false-type-alist1 w
                                                    pot-lst pt backchain-limit))
                                                  (t false-type-alist1))))
                                           (false-type-alist3
                                            (and (not (eq ignore :fta))
                                                 (cond
                                                  ((or (ts= ts1 *ts-t*)
                                                       (ts= ts1 *ts-nil*)
                                                       (ts= ts1 *ts-zero*)

; See the Essay on Strong Handling of *ts-one*, above.

                                                       (and (ts= ts1 *ts-one*)
                                                            (or (variablep arg2)
                                                                (assoc-equal arg2
                                                                             type-alist))))
                                                   (extend-with-proper/improper-cons-ts-tuple
                                                    arg2
                                                    (ts-intersection
                                                     ts2
                                                     (ts-complement ts1))
                                                    (if shared-ttree-tta-p
                                                        shared-ttree
                                                      (cons-tag-trees ttree xttree))
                                                    force-flg dwp type-alist ancestors
                                                    ens false-type-alist2 w
                                                    pot-lst pt backchain-limit))
                                                  (t false-type-alist2)))))
                                      (mv-atf xnot-flg nil nil
                                              true-type-alist3 false-type-alist3
                                              nil nil))))))))))))))))))))
           ((eq (ffn-symb x) '<)
            (mv-let
              (ts0 ttree)
              (type-set-rec x force-flg
                            dwp
                            type-alist ancestors ens w nil
                            pot-lst pt backchain-limit)
              (cond
               ((ts= ts0 *ts-nil*)
                (mv-atf xnot-flg nil t nil type-alist ttree xttree))
               ((ts-disjointp ts0 *ts-nil*)
                (mv-atf xnot-flg t nil type-alist nil ttree xttree))
               (t
                (mv-let
                  (ts1 ttree)
                  (type-set-rec (fargn x 1) force-flg
                                dwp
                                type-alist ancestors ens w nil
                                pot-lst pt backchain-limit)
                  (mv-let
                    (ts2 ttree)
                    (type-set-rec (fargn x 2) force-flg
                                  dwp
                                  type-alist ancestors ens w ttree
                                  pot-lst pt backchain-limit)

; In the mv-let below we effectively implement the facts that, when x
; is of type *ts-integer* (< x 1) is ~(< 0 x), and (< -1 x) is ~(< x
; 0).  By normalizing such inequalities around 0 we can more easily
; recognize the ones covered by our built in types.

; WARNING: A bug once lurked here, so beware.  The term we are
; assuming is represented by xnot-flg and x.  We are about to
; re-represent it in terms of not-flg, arg1 and arg2.  Do not
; accidentally use not-flg with x or xnot-flg with (< arg1 arg2)!  In
; the old code, we had only one name for these two flgs.

                    (mv-let
                      (not-flg arg1 arg2 ts1 ts2)
                      (cond ((and (equal (fargn x 2) *1*)
                                  (ts-subsetp ts1
                                              (ts-union (ts-complement
                                                         *ts-acl2-number*)
                                                        *ts-integer*)))
                             (mv (not xnot-flg) *0* (fargn x 1) *ts-zero* ts1))
                            ((and (equal (fargn x 2) *2*)
                                  (ts-subsetp ts1
                                              (ts-union (ts-complement
                                                         *ts-acl2-number*)
                                                        *ts-integer*)))
                             (mv (not xnot-flg) *1* (fargn x 1) *ts-one* ts1))
                            ((and (equal (fargn x 1) *-1*)
                                  (ts-subsetp ts2
                                              (ts-union (ts-complement
                                                         *ts-acl2-number*)
                                                        *ts-integer*)))
                             (mv (not xnot-flg) (fargn x 2) *0* ts2 *ts-zero*))
                            (t (mv xnot-flg (fargn x 1) (fargn x 2) ts1 ts2)))

; Foreshadow 1: Note that if neither of the newly bound arg1 nor arg2 is *0*
; and arg1 is not *1* then not-flg is xnot-flg and arg1 and arg2 are the
; corresponding arguments of x.  That is because on all but the last branch of
; the cond above, arg1 or arg2 is set to *0* or arg1 is set to *1*.  We use
; this curious fact below.

; In the mv-let below we effectively implement the fact that, when x is of type
; *ts-integer* (< 0 (+ 1 x)) is ~(< x 0).  The symmetric equivalence of (< (+
; -1 x) 0) to ~(< 0 x) is also handled.

; We will assume that the binary-+ has been commuted so that the constant arg,
; if any, is the first.

; Note that the output of this transformation is not subject to the first
; transformation, above, so we do not have to consider repeating that
; transformation.  However, it is conceivable that the output of this
; transformation is subject to its symmetric counterpart.  In particular, if we
; composed this transformation with itself we might reduce (< 0 (+ 1 (+ -1 x)))
; to (< 0 x).  We prefer instead to take the position that some arithmetic
; simplifier will reduce the +-expressions.

                      (mv-let
                        (not-flg arg1 arg2 ts1 ts2 ttree)
                        (cond ((and (equal arg1 *0*)
                                    (ts-subsetp ts2

; It is sound to use (ts-intersection ts2 *ts-acl2-number*) in place of ts2
; above, but since below we see that arg2 is a call of binary-+, we know that
; ts2 is already contained in *ts-acl2-number*.

                                                *ts-integer*)
                                    (ffn-symb-p arg2 'binary-+)
                                    (equal (fargn arg2 1) *1*))

; So the term is of the form (< 0 (+ 1 x)) and we know x is some integer (or a
; non-number).  We transform it to ~(< x 0).  But we must determine the
; type-set of x.  It cannot be done merely by inverting the type-set of (+ 1
; x): the latter might be *ts-integer* and x could either be
; *ts-non-positive-integer* or *ts-integer*, or even a non-number.  Some cases
; we could invert:  if (+ 1 x) is non-positive, then we know x must be strictly
; negative.  But rather than invert, we just call type-set on x, accreting onto
; the existing ttree.

                               (mv-let (tsx ttree)
                                 (type-set-rec (fargn arg2 2) force-flg
                                               dwp
                                               type-alist
                                               ancestors ens w ttree
                                               pot-lst pt backchain-limit)
                                 (mv (not not-flg) (fargn arg2 2) *0*
                                     tsx *ts-zero* ttree)))
                              ((and (equal arg2 *0*)
                                    (ts-subsetp ts1 *ts-integer*)
                                    (ffn-symb-p arg1 'binary-+)
                                    (equal (fargn arg1 1) *-1*))
                               (mv-let (tsx ttree)
                                 (type-set-rec (fargn arg1 2) force-flg
                                               dwp
                                               type-alist
                                               ancestors ens w ttree
                                               pot-lst pt backchain-limit)
                                 (mv (not not-flg) *0* (fargn arg1 2) *ts-zero*
                                     tsx ttree)))
                              (t (mv not-flg arg1 arg2 ts1 ts2 ttree)))

; Foreshadow 2:  Observe that if, at this point, neither the newly bound arg1
; nor the newly bound arg2 is *0*, then the newly bound not-flg, arg1 and arg2
; are all equal to their old values (outside this mv-let).  That is because the
; cond above, which determines the new values of not-flg, arg1 and arg2 here,
; has the property that on the two branches that changes the not-flg, one of
; the two args is set to *0*.  If neither arg is *0* then we could have only
; come out on the last clause of the cond above and not-flg etc are thus
; unchanged.  We use this curious property below.

; The transformations just carried out have the possibly odd effect of
; assuming (< 0 x) false when asked to assume (< x 1) true, for integral x.
; This effectively sets x's type-set to the non-positives.  One might
; then ask, what happens if we later decide to get the type-set of (<
; x 1).  We would hope that, having assumed it, we would realize it
; was true!  Indeed we do, but only because type-set-< makes the same
; normalization of (< x 1).  This raises the question: Could we reduce
; the size of our code by doing the normalization in only one place,
; either here in assume-true-false or there in type-set-<?  The real
; reason we do it in both places has nothing to do with the subtleties
; discussed here; there is no guarantee that both of these functions
; will be called.  If (< x 1) appears in a test, we will call
; assume-true-false on it and we have to normalize it to produce the
; desired tta and fta.  If (< x 1) appears as the entire resultant
; term, we'll just call type-set on it and we have to normalize it to
; decide it.

; Another question raised is: "What about the second transformation done
; above?"  We assume ~(< x 0) when asked to assume (< 0 (+ 1 x)), with the
; effect that x is given (roughly) the type-set non-negative integer.  Note
; that type-set-< does not make this second transformation.  Will we recognize
; (< 0 (+ 1 x)) as true later?  Yes.  If x is non-negative, then type-set
; determines that (+ 1 x) is positive and hence (< 0 (+ 1 x)) is true.

                        (cond
                         ((equal arg1 *0*)
                          (cond
                           ((ts-subsetp ts2
                                        #+:non-standard-analysis *ts-positive-real*
                                        #-:non-standard-analysis *ts-positive-rational*)
                            (mv-atf not-flg t nil type-alist nil
                                    ttree
                                    xttree))
                           ((ts-subsetp ts2
                                        (ts-union (ts-complement *ts-acl2-number*)
                                                  #+:non-standard-analysis
                                                  *ts-non-positive-real*
                                                  #-:non-standard-analysis
                                                  *ts-non-positive-rational*))
                            (mv-atf not-flg nil t nil type-alist
                                    ttree
                                    xttree))
                           (t
                            (let* ((shared-ttree (cons-tag-trees ttree xttree))
                                   (ignore (adjust-ignore-for-atf not-flg ignore0))
                                   (true-type-alist
                                    (and (not (eq ignore :tta))
                                         (extend-type-alist
                                          ;;*** -simple
                                          arg2
                                          (ts-intersection
                                           ts2
                                           #+:non-standard-analysis
                                           (ts-union *ts-positive-real*
                                                     *ts-complex*)
                                           #-:non-standard-analysis
                                           (ts-union *ts-positive-rational*
                                                     *ts-complex-rational*))
                                          shared-ttree type-alist w)))
                                   (false-type-alist
                                    (and (not (eq ignore :fta))
                                         (extend-type-alist
                                          ;;*** -simple
                                          arg2
                                          (ts-intersection
                                           ts2 (ts-complement
                                                #+:non-standard-analysis
                                                *ts-positive-real*
                                                #-:non-standard-analysis
                                                *ts-positive-rational*))
                                          shared-ttree type-alist w))))

; We formerly put the inequality explicitly on the type-alist only in
; the case that (ts-intersectp ts2 *ts-complex-rational*).  We leave
; in place the comment regarding that case, below.  However, we now
; put the inequality on the type-alist in all cases, in order to
; assist in relieving hypotheses involving free variables.  Robert
; Krug sent the following relevant example.


;;; (defstub foo (x) t)
;;;
;;; (defaxiom test1
;;;   (implies (and (<= 0 x)
;;;                 (rationalp x))
;;;            (foo y)))
;;;
;;; (thm
;;;  (implies (and (rationalp x)
;;;                (<= 0 x))
;;;           (foo y)))

; The thm fails, because the hypothesis of test1 is not relieved.  The
; following trace excerpt shows why.

;;;  1> (SEARCH-TYPE-ALIST (< X '0)    ; Attempt to find that (< X 0)
;;;                        64          ; is false.  Note:
;;;                                    ; (decode-type-set 64) = '*TS-NIL*
;;;                        ((X 7))     ; Type-alist:  X is a non-negative
;;;                                    ; rational.  Note:
;;;                                    ; (decode-type-set 7) =
;;;                                    ; *TS-NON-NEGATIVE-RATIONAL*
;;;                        ((Y . Y))   ; unify-subst
;;;                        NIL)>       ; ttree
;;;  <1 (SEARCH-TYPE-ALIST NIL ((Y . Y)) NIL)>   ; failed to relieve hyp

; As seen below, assume-true-false had failed to put the inequality
; explicitly on the type-alist.

;;;  1> (ASSUME-TRUE-FALSE (< X '0) ; condition assumed true or false
;;;                        NIL      ; a tag-tree
;;;                        NIL      ; force-flg
;;;                        NIL      ; never mind this one...
;;;                        ((X 31)) ; type-alist: X is rational
;;;                        NIL      ; ancestors
;;;                        |some-enabled-structure|
;;;                        |current-acl2-world|)>
;;;  <1 (ASSUME-TRUE-FALSE NIL             ; must-be-true
;;;                        NIL             ; must-be-false
;;;                        ((X 24) (X 31)) ; true-type-alist:
;;;                                        ; X is negative rational
;;;                        ((X 7) (X 31))  ; false-type-alist:
;;;                                        ; X is non-negative rational
;;;                        NIL)>           ; tag-tree

; But wait, there's more!  Robert subsequently sent an example showing
; that it is not enough to put the current inequality with 0, e.g.,
; (mcons-term* '< *0* arg2), on the type-alist.  The original equality
; may need to be there as well.  Here is his example, which ACL2 can
; now prove (see mv-atf-2).

;;; (defstub foo (x) t)
;;;
;;; (defaxiom test
;;;   (implies (and (<= 1 x)
;;;                 (integerp x))
;;;            (foo y)))
;;;
;;; (thm
;;;   (implies (and (integerp x)
;;;                 (<= 1 x))
;;;            (foo y)))

; Start old comment regarding the case that (ts-intersectp ts2
; *ts-complex-rational*).

; Long comment on why we extend the true-type-alist to accommodate complex
; numbers.

; For an example that illustrates why we need to put (mcons-term* '< *0* arg2)
; on the true-type-alist explicitly in this case, try the following.

;;; (encapsulate
;;;  (((foo *) => *))
;;;  (local (defun foo (x) (<= 0 x)))
;;;  (defthm foo-type (implies (<= 0 x) (equal (foo x) t))
;;;    :rule-classes :type-prescription))
;;;
;;; (thm (implies (<= 0 x) (equal (foo x) t)))

; If we simply use true-type-alist here, we'll lose the information that (< 0
; arg2).  That is, we desire that the true-type-alist is sufficient for
; deducing what we are assuming true; but if arg2 can be a complex number, we
; will not be able to make that determination.  So, we put this inequality on
; the type-alist, explicitly.  We do so in the order shown for two reasons,
; probably neither of them particularly important (but at least, we document
; what they are).  For one, we want type-set to find the explicit inequality
; first, in case it ever tries to decide it.  Although we do not expect
; type-set to have any trouble even if we bury the inequality after an entry
; for arg2, this coding seems more robust.  More importantly, however, we want
; to call extend-type-alist, which is a bit complicated, on as short a
; type-alist as possible.

; End old comment regarding the case that (ts-intersectp ts2
; *ts-complex-rational*).

                              (mv-atf-2 not-flg true-type-alist false-type-alist
                                        (mcons-term* '< *0* arg2)
                                        xnot-flg x shared-ttree xttree ignore)))))
                         ((equal arg1 *1*)
                          (cond
                           ((ts-subsetp ts2 *ts-integer>1*)
                            (mv-atf not-flg t nil type-alist nil
                                    ttree
                                    xttree))
                           ((ts-subsetp ts2
                                        (ts-union (ts-complement *ts-acl2-number*)
                                                  *ts-one*
                                                  *ts-non-positive-rational*))
                            (mv-atf not-flg nil t nil type-alist
                                    ttree
                                    xttree))
                           (t
                            (let* ((shared-ttree (cons-tag-trees ttree xttree))
                                   (ignore (adjust-ignore-for-atf not-flg ignore0))
                                   (true-type-alist
                                    (and (not (eq ignore :tta))
                                         (extend-type-alist
                                          ;;*** -simple
                                          arg2
                                          (ts-intersection
                                           ts2
                                           (ts-union *ts-integer>1*
                                                     *ts-positive-ratio*
                                                     *ts-complex-rational*))
                                          shared-ttree type-alist w)))
                                   (false-type-alist
                                    (and (not (eq ignore :fta))
                                         (if (variablep arg2)

; By restricting to variables here, we avoid a failed proof for lemma LEMMA3 in
; community book books/data-structures/memories/memtree.lisp (and perhaps other
; failed proofs).  This weakened heuristic seems consistent with the spirit of
; the Essay on Strong Handling of *ts-one*, above.

                                             (extend-type-alist
                                              ;;*** -simple
                                              arg2
                                              (ts-intersection
                                               ts2
                                               (ts-complement *ts-integer>1*))
                                              shared-ttree type-alist w)
                                           type-alist))))
                              (mv-atf-2 not-flg true-type-alist false-type-alist
                                        (mcons-term* '< *1* arg2)
                                        xnot-flg x shared-ttree xttree ignore)))))
                         ((equal arg2 *0*)
                          (cond
                           ((ts-subsetp ts1
                                        #+:non-standard-analysis
                                        *ts-negative-real*
                                        #-:non-standard-analysis
                                        *ts-negative-rational*)
                            (mv-atf not-flg t nil type-alist nil
                                    ttree
                                    xttree))
                           ((ts-subsetp ts1
                                        (ts-union (ts-complement *ts-acl2-number*)
                                                  #+:non-standard-analysis
                                                  *ts-non-negative-real*
                                                  #-:non-standard-analysis
                                                  *ts-non-negative-rational*))
                            (mv-atf not-flg nil t nil type-alist
                                    ttree
                                    xttree))
                           (t
                            (let* ((shared-ttree (cons-tag-trees ttree xttree))
                                   (ignore (adjust-ignore-for-atf not-flg ignore0))
                                   (true-type-alist
                                    (and (not (eq ignore :tta))
                                         (extend-type-alist
                                          ;;*** -simple
                                          arg1
                                          (ts-intersection
                                           ts1
                                           #+:non-standard-analysis
                                           (ts-union *ts-negative-real*
                                                     *ts-complex*)
                                           #-:non-standard-analysis
                                           (ts-union *ts-negative-rational*
                                                     *ts-complex-rational*))
                                          shared-ttree type-alist w)))
                                   (false-type-alist
                                    (and (not (eq ignore :fta))
                                         (extend-type-alist
                                          ;;*** -simple
                                          arg1
                                          (ts-intersection
                                           ts1 (ts-complement
                                                #+:non-standard-analysis
                                                *ts-negative-real*
                                                #-:non-standard-analysis
                                                *ts-negative-rational*))
                                          shared-ttree type-alist w))))
                              (mv-atf-2 not-flg true-type-alist false-type-alist
                                        (mcons-term* '< arg1 *0*)
                                        xnot-flg x shared-ttree xttree ignore)))))
                         (t (mv-let
                              (mbt mbf tta fta dttree)
                              (assume-true-false1
                               xnot-flg ; = not-flg
                               x        ; = (mcons-term* '< arg1 arg2)

; Once upon a time we had (mcons-term* '< arg1 arg2), above, instead of x.  But
; we claim that not-flg is xnot-flg and that arg1 and arg2 are the
; corresponding arguments of x so that x is equal to (mcons-term* '< arg1
; arg2).  The proof is as follows.  We are in the t clause of a cond.  The
; preceding tests establish that neither arg1 nor arg2 is *0* here, nor is arg1
; *1* here.  Hence, by Foreshadow 2 above we conclude that not-flg, arg1 and
; arg2 are unchanged from their values at Foreshadow 1.  But at Foreshadow 1 we
; see that if neither arg is *0* and arg1 is not *1*, then not-flg is xnot-flg
; and arg1 and arg2 are the corresponding components of x.  Q.E.D.

                               xttree force-flg dwp type-alist ancestors ens w
                               pot-lst pt backchain-limit)

; Inefficiency: It is somewhat troubling that we are holding ts1 and
; ts2 in our hands while invoking assume-true-false1 on (< arg1 arg2),
; knowing full-well that it will recompute ts1 and ts2.  Sigh.  It
; would be nice to avoid this duplication of effort.

; We could now return (mv mbt mbf tta fta dttree) as the answer.  But, in the
; case that mbt and mbf are both nil we want to tighten up the returned
; type-alists a little if we can.  Suppose we are dealing with (< a1 a2) and a1
; is known to be positive.  Then a2 is (even more) positive.  We can add that
; to the tta, if it changes the type-set of a2.

                              (cond
                               ((or mbt mbf)

; Just return the already computed answers if we've settled the
; question.

                                (mv mbt mbf tta fta dttree))
                               (t (let ((tta
                                         (and (not (eq ignore0 :tta))
                                              (assume-true-false-<
                                               not-flg
                                               arg1 arg2 ts1 ts2 tta ttree xttree w)))
                                        (fta
                                         (and (not (eq ignore0 :fta))
                                              (assume-true-false-<
                                               (not not-flg)
                                               arg1 arg2 ts1 ts2 fta ttree xttree w))))
                                    (mv nil nil tta fta nil)))))))))))))))
           ((equivalence-relationp (ffn-symb x) w)
            (let ((arg1 (fargn x 1))
                  (arg2 (fargn x 2)))
              (cond
               ((equal arg1 arg2)
                (mv-atf xnot-flg t nil type-alist nil nil (puffert xttree)))
               (t
                (let ((equiv (ffn-symb x)))
                  (mv-let
                    (occursp1 canonicalp1 arg1-canon ttree1)
                    (canonical-representative equiv arg1 type-alist)
                    (cond
                     ((and occursp1

; See comment in the 'equal case for an explanation of this use of occursp1
; and a similar use of occursp2 below.

                           (equal arg1-canon arg2))
                      (mv-atf xnot-flg t nil type-alist nil
                              nil
                              (puffert
                               (cons-tag-trees ttree1 xttree))))
                     (t (mv-let
                          (occursp2 canonicalp2 arg2-canon ttree2)
                          (canonical-representative equiv arg2 type-alist)
                          (cond
                           ((and occursp2 (equal arg1-canon arg2-canon))
                            (mv-atf xnot-flg t nil type-alist nil
                                    nil
                                    (puffert
                                     (cons-tag-trees
                                      xttree
                                      (cons-tag-trees ttree1 ttree2)))))
                           (t
                            (let ((temp-temp
                                   (assoc-equiv equiv arg1-canon arg2-canon
                                                type-alist)))
                              (cond
                               (temp-temp
                                (cond ((ts= (cadr temp-temp) *ts-t*)

; See comment in corresponding place in the 'equal case.

                                       (mv-atf (er hard 'assume-true-false
                                                   "Please send the authors of ~
                                               ACL2 a replayable transcript ~
                                               of this problem if possible, ~
                                               so that they can see what went ~
                                               wrong in the function ~
                                               assume-true-false.  The ~
                                               offending call was ~x0.  The ~
                                               surprising type-set arose from ~
                                               a call of ~x1."
                                                   (list 'assume-true-false
                                                         (kwote x) '<xttree>
                                                         force-flg
                                                         (kwote type-alist)
                                                         '<ens> '<w>)
                                                   (list 'assoc-equiv
                                                         (kwote equiv)
                                                         (kwote arg1-canon)
                                                         (kwote arg2-canon)
                                                         '<same_type-alist>))
                                               nil nil nil nil nil nil))
                                      ((ts= (cadr temp-temp) *ts-nil*)
                                       (mv-atf xnot-flg nil t nil type-alist
                                               nil
                                               (if (and canonicalp1 canonicalp2)
                                                   (cons-tag-trees (cddr temp-temp)
                                                                   xttree)
                                                 (puffert
                                                  (cons-tag-trees
                                                   (cddr temp-temp)
                                                   (cons-tag-trees
                                                    ttree1
                                                    (cons-tag-trees ttree2 xttree)))))))
                                      (t
                                       (let ((erp (assume-true-false-error
                                                   type-alist x (cadr temp-temp))))
                                         (mv erp nil nil nil nil)))))
                               (t
                                (let ((swap-flg
                                       (term-order arg1-canon arg2-canon))
                                      (xttree+
                                       (if (and canonicalp1 canonicalp2)
                                           xttree
                                         (puffert
                                          (cons-tag-trees
                                           ttree1
                                           (cons-tag-trees ttree2 xttree))))))
                                  (mv-atf xnot-flg nil nil
                                          (and (not (eq ignore :tta))
                                               (extend-type-alist1
                                                equiv occursp1 occursp2
                                                (and canonicalp1 canonicalp2)
                                                arg1-canon arg2-canon swap-flg x
                                                *ts-t* xttree+ type-alist))
                                          (and (not (eq ignore :fta))
                                               (extend-type-alist1
                                                equiv occursp1 occursp2
                                                (and canonicalp1 canonicalp2)
                                                arg1-canon arg2-canon swap-flg x
                                                *ts-nil* xttree+ type-alist))
                                          nil nil))))))))))))))))
           ((or (eq (ffn-symb x) 'car)
                (eq (ffn-symb x) 'cdr))

; In this comment we assume (ffn-symb x) is car but everything we say is true
; for the cdr case as well.  Suppose xnot-flg is nil.  Then after the
; assume-true-false1 below, tta is the result of assuming (car arg) non-nil.
; But if (car arg) is non-nil, then arg is non-nil too.  That is, (implies (car
; arg) arg) is a theorem: Pf.  Consider the contrapositive, (implies (not arg)
; (not (car arg))). Q.E.D.  So we assume arg onto tta as well as (car arg).
; Fta, on the other hand, is the result of assuming (car arg) nil.  That tells
; us nothing about arg, e.g., arg could be nil, a cons (whose car is nil) or
; anything violating car's guard.  Summarizing this case: if xnot-flg is nil,
; then we assume both (car arg) and arg non-nil onto tta and assume only (car
; arg) nil onto fta.

; Now on the other hand, suppose xnot-flg is t.  Then tta contains
; the assumption that (car arg) is nil and fta contains the
; assumption that (car arg) is non-nil.  We can add to fta the
; assumption that arg is non-nil.  Observe that the two cases are
; symmetric if we simply swap the role of tta and fta before we start
; and after we are done.  The first swap is done by the let below.
; The second is done by mv-atf.

            (mv-let (mbt mbf tta fta ttree)
              (assume-true-false1
               xnot-flg x xttree force-flg dwp type-alist ancestors ens w
               pot-lst pt backchain-limit)
              (cond ((or mbt mbf)
                     (mv mbt mbf tta fta ttree))
                    (t (let ((tta (if xnot-flg fta tta))
                             (fta (if xnot-flg tta fta)))
                         (mv-let (mbt1 mbf tta1 fta1 ttree)
                           (assume-true-false-rec
                            (fargn x 1)
                            xttree force-flg dwp tta ancestors ens w
                            pot-lst pt :fta backchain-limit)
                           (declare (ignore mbt1 fta1))
                           (mv-atf xnot-flg mbt mbf tta1 fta
                                   ttree nil)))))))
           ((eq (ffn-symb x) 'IF)
            (assume-true-false-if xnot-flg x xttree force-flg dwp
                                  type-alist ancestors ens w
                                  pot-lst pt backchain-limit))
           (t (assume-true-false1 xnot-flg x xttree
                                  force-flg dwp type-alist ancestors ens
                                  w
                                  pot-lst pt backchain-limit)))))))))

(defun assume-true-false1 (not-flg x xttree force-flg dwp type-alist ancestors
                                   ens w pot-lst pt backchain-limit)

; Roughly speaking, this is the simple assume-true-false, which just
; computes the type-set of x and announces that x must be t, must be
; f, or else announces neither and creates two new type-alists with x
; bound to its type minus *ts-t* and to *ts-nil*.  It returns the
; standard 5 results of assume-true-false.  It puts xttree into the
; type-alist entries for x, if any.

; See assume-true-false.

; NOTE:  This function should not be called when x could be a call of an
; equivalence relation, since otherwise it may destroy the third invariant on
; type-alists.

  (mv-let (ts ttree)
          (type-set-rec x force-flg
                        dwp
                        type-alist ancestors ens w nil
                        pot-lst pt backchain-limit)

; If we can decide x on the basis of ts, do so and report use of ttree.
; Xttree will be put in by mv-atf.

          (cond ((ts= ts *ts-nil*)
                 (mv-atf not-flg nil t nil type-alist ttree xttree))
                ((ts-disjointp ts *ts-nil*)
                 (mv-atf not-flg t nil type-alist nil ttree xttree))
                (t

; We produce two new type-alists.  In the one in which x is assumed
; true, we annotate the entry with a ttree that includes both
; xttree and ttree, the initial type-set of x.  In the one in
; which x is assumed false, we annotate the entry with the ttree that
; includes just xttree.  The true entry depends on the old type
; because we intersect the old and non-nil.  But the false entry is
; just the nil type and doesn't depend on the old one.

                 (mv-atf not-flg nil nil
                         (extend-with-proper/improper-cons-ts-tuple
                          x
                          (ts-intersection ts *ts-non-nil*)
                          (cons-tag-trees ttree xttree)
                          force-flg dwp type-alist ancestors ens
                          type-alist w
                          pot-lst pt backchain-limit)

; It is legal to call extend-type-alist-simple below because we know that x is
; not the call of an equivalence relation.  However, the call of
; extend-with-proper/improper-cons-ts-tuple above cannot quite be safely
; simplified, because perhaps x is a final CDR that is the call of an
; equivalence relation.

                         (extend-type-alist-simple
                          x *ts-nil* xttree type-alist)
                         nil nil)))))

(defun proper/improper-cons-ts-tuple (term ts ttree force-flg dwp type-alist
                                           ancestors ens wrld pot-lst pt
                                           backchain-limit)

; We return a tuple of the form (mv term' ts' ttree') that asserts the
; assumption that term has type set ts (with the given ttree
; attached).  Most often, term', ts' and ttree' are just term, ts and
; ttree.  However, if term is of the form (cons a x) we do certain
; auxiliary processing related to the existence of *ts-true-list* and
; its subtypes.  We guarantee that ttree' includes ttree.

; We make various implicit assumptions about term and ts, all
; summarized by the restriction that this function can only be called
; by assume-true-false after checking the current type-set of term and
; failing to decide the question.

; We start with two examples.  Suppose term is (cons a1 x) and ts is
; *ts-true-list*.  Then the "various implicit assumptions" are
; violated because assume-true-false would never ask us to do this:
; the type-set of term is, at worst, the union of *ts-proper-cons* and
; *ts-improper-cons*, and certainly doesn't include *ts-nil*.  But
; assume-true-false always asks us to assume a type-set that is a
; subset of the current type-set.

; So suppose we are asked to assume that (cons a1 x) is of type
; *ts-proper-cons*.  Then we can deduce that x is of type
; *ts-true-list*.  Indeed, these two are equivalent because if we
; store the latter we can compute the former with type-set.  But
; because x is a subterm of (cons a1 x) we prefer to store the
; assumption about x because it will find greater use.  However, we
; may already know something about the type of x.  For example, x may
; be known to be non-nil.  So we are obliged to intersect the old type
; of x with the newly derived type if we want to keep maximizing what
; we know.  Because of the "implicit assumptions" this intersection
; will never produce the empty type set: if it is impossible for x to
; have the required type, then assume-true-false better not ask us to
; make the assumption.  For example, if x is known not to be a
; true-list, then assume-true-false would never ask us to assume that
; (cons a1 x) is proper.

; The example above is based on the theorem
;    (proper-consp (cons a1 x))   <-> (true-listp x).
; We similarly build in the theorem
;    (improper-consp (cons a1 x)) <-> (not (true-listp x)).

  (cond
   ((and (ffn-symb-p term 'cons)
         (or (ts= ts *ts-proper-cons*)
             (ts= ts *ts-improper-cons*)))
    (let* ((x (non-cons-cdr term)))

; Can x be an explicit value?  If it can, then we'd be in trouble because
; we return a type-alist binding that sets the value of x.  But in fact
; x cannot be an explicit value.  If it were, then assume-true-false
; would have decided whether (cons a x) was proper or improper.

      (mv-let (tsx ttreex)
              (type-set-rec x force-flg
                            dwp
                            type-alist ancestors ens wrld ttree
                            pot-lst pt backchain-limit)
              (cond
               ((ts= ts *ts-proper-cons*)
                (mv x
                    (ts-intersection tsx *ts-true-list*)
                    ttreex))
               (t
                (mv x
                    (ts-intersection tsx (ts-complement *ts-true-list*))
                    ttreex))))))
   (t (mv term ts ttree))))

(defun extend-with-proper/improper-cons-ts-tuple
  (term ts ttree force-flg dwp type-alist ancestors ens
        type-alist-to-be-extended wrld pot-lst pt backchain-limit)

; Programming Note:

; Our convention is to call this function to extend the type-alist unless we
; know that the supplied ts is neither *ts-proper-cons* nor *ts-improper-cons*.
; That is, we use this function to construct type-alist entries in only some of
; the cases.  See also extend-type-alist-simple and extend-type-alist.

  (mv-let (term ts ttree)
          (proper/improper-cons-ts-tuple term ts ttree force-flg dwp
                                         type-alist ancestors ens wrld
                                         pot-lst pt backchain-limit)
          (extend-type-alist term ts ttree type-alist-to-be-extended wrld)))

)

(defun type-set (x force-flg dwp type-alist ens w ttree pot-lst pt)

; See type-set-rec.

  (type-set-rec x force-flg dwp type-alist
                nil ; ancestors
                ens w ttree
                pot-lst pt
                (backchain-limit w :ts)))

(defun type-set-bc (x force-flg dwp type-alist ens w ttree pot-lst pt
                      ts-backchain-limit)

; See type-set-rec.

  (type-set-rec x force-flg dwp type-alist
                nil ; ancestors
                ens w ttree
                pot-lst pt
                ts-backchain-limit))

(defstub assume-true-false-aggressive-p () t)
(defattach assume-true-false-aggressive-p constant-nil-function-arity-0)

(defun top-level-if-reduce-rec (test term not-flg ts)

; See top-level-if-reduce.  We return (mv changedp reduced-term), where if
; changedp is nil, then reduced-term is EQ to term.

  (cond ((ffn-symb-p term 'if)
         (cond ((equal test (fargn term 1))
                (mv t (if not-flg (fargn term 3) (fargn term 2))))
               ((and (ffn-symb-p (fargn term 1) 'not)
                     (equal test (fargn (fargn term 1) 1)))
                (mv t (if not-flg (fargn term 2) (fargn term 3))))
               (t (mv-let (changedp-tbr tbr)
                    (top-level-if-reduce-rec test (fargn term 2) not-flg ts)
                    (mv-let (changedp-fbr fbr)
                      (top-level-if-reduce-rec test (fargn term 3) not-flg ts)
                      (cond ((or changedp-tbr changedp-fbr)
                             (mv t
                                 (cond ((equal tbr fbr)
                                        tbr)
                                       ((and (equal tbr *t*)
                                             (equal fbr *nil*)
                                             (ts= ts (ts-complement *ts-nil*)))

; (thm (equal (not (equal (if x t nil) nil)) (not (equal x nil))))

                                        (fargn term 1))
                                       ((and (equal tbr *nil*)
                                             (equal fbr *t*)
                                             (ts= ts *nil*)
                                             (ffn-symb-p (fargn term 1) 'not))

; (thm (equal (equal (if (not x) nil t) nil) (equal x nil)))

                                        (fargn (fargn term 1) 1))
                                       (t
                                        (fcons-term* 'if (fargn term 1) tbr fbr)))))
                            (t (mv nil term))))))))
        (t (mv nil term))))

(defun top-level-if-reduce (test term not-flg ts)

; Reduce top-level subterms of term under the assumption that test is true if
; not-flg is nil, or under the assumption that test is false if not-flg is
; true, so that (if not-flg (not test) test) has type ts if and only if the
; result has type ts.  (Here, "top-level" is in the sense of the if-then-else
; structure: we continue the search only through true and false branches of IF
; calls.)  Specifically: we reduce each top-level subterm (if test tbr fbr) to
; tbr if not-flg is false, else to fbr; we reduce each top-level subterm (if
; (not test) tbr fbr) to fbr if not-flg is true, else to tbr; and we do a few
; additional reductions to simplify certain if-subterms.

; For efficiency, it may be a good idea first to call (top-level-if-p test
; term) to determine whether there is any such opportunity for reduction,
; before doing the more elaborate term walk of top-level-if-reduce-rec.

  (mv-let (changedp val)
    (top-level-if-reduce-rec test term not-flg ts)
    (declare (ignore changedp))
    val))

(defun top-level-if-p (test term)

; Return true when either test or its negation occurs as a top-level IF test in
; term.

  (cond ((ffn-symb-p term 'if)
         (or (equal test (fargn term 1))
             (and (ffn-symb-p (fargn term 1) 'not)
                  (equal test (fargn (fargn term 1) 1)))
             (top-level-if-p test (fargn term 2))
             (top-level-if-p test (fargn term 3))))
        (t nil)))

(defun type-alist-reducible-entries (term type-alist bound)

; Return a list of entries (term2 ts . ttree) in type-alist for which term or
; (not term) is a top-level test of term2.  Bound is a natural number or nil;
; we look for up to bound-many entries, except that nil represents that there
; is no bound.

  (cond
   ((or (endp type-alist)
        (and bound (zp bound)))
    nil)
   (t
    (let* ((rest-type-alist (cdr type-alist))
           (bound-1 (and bound (1- bound)))
           (entry (car type-alist))
           (term2 (car entry)))
      (cond
       ((top-level-if-p term term2)
        (cons entry
              (type-alist-reducible-entries term rest-type-alist bound-1)))
       (t (type-alist-reducible-entries term rest-type-alist bound-1)))))))

(defun assume-true-false-aggressive-1 (entries tta fta x xttree wrld ignore0
                                               not-flg)
  (cond
   ((endp entries)
    (mv nil nil tta fta nil))
   (t
    (let* ((entry (car entries))
           (term (car entry))
           (ts (cadr entry))
           (new-ttree (cons-tag-trees xttree (cddr entry)))
           (new-tta
            (if (eq ignore0 :tta)
                tta
              (extend-type-alist (top-level-if-reduce x term not-flg ts)
                                 ts new-ttree tta wrld)))
           (new-fta
            (if (eq ignore0 :fta)
                fta
              (extend-type-alist (top-level-if-reduce x term (not not-flg) ts)
                                 ts new-ttree fta wrld))))
      (assume-true-false-aggressive-1
       (cdr entries) new-tta new-fta x xttree wrld ignore0 not-flg)))))

(defun assume-true-false-aggressive (x xttree force-flg dwp type-alist
                                       ens w pot-lst pt
                                       ignore0 ts-backchain-limit
                                       bound)
  (mv-let
    (mbt mbf tta fta ttree)
    (assume-true-false-rec x xttree force-flg dwp type-alist
                           nil ; ancestors
                           ens w pot-lst pt ignore0
                           ts-backchain-limit)
    (cond
     ((or mbt mbf)
      (mv mbt mbf tta fta ttree))
     (t
      (mv-let (not-flg atm)
        (strip-not x)
        (let ((entries
               (type-alist-reducible-entries atm
                                             type-alist
                                             (and (natp bound) bound))))
          (assume-true-false-aggressive-1
           entries

; Each member of entries subsumes some member of the given type-alist.  It is
; tempting not to bother removing them from tta or fta.  But we have seen a
; case where without these removals, the type-alist exploded to more than
; 1,000,000 entries, ultimately causing a stack overflow with top-level-if-p,
; when assume-true-false-aggressive-p was given attachment
; constant-nil-function-arity-0.

           (set-difference-equal tta entries)
           (set-difference-equal fta entries)
           atm xttree w ignore0 not-flg)))))))

(defun assume-true-false (x xttree force-flg dwp type-alist ens w pot-lst pt
                            ignore0)
  (let ((bound (assume-true-false-aggressive-p)))
    (cond
     (bound
      (assume-true-false-aggressive x xttree force-flg dwp type-alist
                                    ens w pot-lst pt ignore0
                                    (backchain-limit w :ts)
                                    bound))
     (t
      (assume-true-false-rec x xttree force-flg dwp type-alist
                             nil ; ancestors
                             ens w pot-lst pt ignore0
                             (backchain-limit w :ts))))))

(defun assume-true-false-bc (x xttree force-flg dwp type-alist ens w pot-lst pt
                               ignore0 ts-backchain-limit)
  (let ((bound (assume-true-false-aggressive-p)))
    (cond
     (bound
      (assume-true-false-aggressive x xttree force-flg dwp type-alist
                                    ens w pot-lst pt ignore0
                                    ts-backchain-limit
                                    bound))
     (t
      (assume-true-false-rec x xttree force-flg dwp type-alist
                             nil ; ancestors
                             ens w pot-lst pt ignore0
                             ts-backchain-limit)))))

(defun ok-to-force-ens (ens)
  (and (enabled-numep *force-xnume* ens)
       t))

; Here is the function used to add an assumption to a ttree.  In principle,
; add-linear-assumption is called by type-set when it needs to force a
; hypothesis; but we don't want to make it mutually recursive with type-set and
; something like it is open coded in type-set.

(defun add-linear-assumption (target term type-alist ens
                                     immediatep force-flg wrld tag-tree)

; Adds the assumption term to the assumptions component of tag-tree, except
; that if the assumption is known to be true or known to be false under the
; type alist or is already in the tree, it is not added.

; This function returns (mv flg tag-tree'), where tag-tree' is the new
; tag-tree and flg is
; a) :known-true if the assumption is known to be true (non-nil);
; b) :known-false if the assumption is known to be false;
; c) :added if the assumption is not known to be true or false and
;    the assumption was added; and
; d) :failed if the assumption is not known to be true or false, but
;    the assumption was not added because force-flg did not permit it.

  (mv-let
   (ts ttree)
   (type-set term force-flg nil type-alist ens wrld nil nil nil)

; Note that force-flg may be t above.  In that case, we force the
; guards of term.  For example, suppose term were (acl2-numberp (+ x y)),
; where x is known rational and y is unknown (and we use + for binary-+).
;  Then ts will come back *ts-t* and the ttree will contain a
; (acl2-numberp y) 'assumption.  If we ultimately rely on ts then we
; must add ttree to the incoming tag-tree.  But if we ultimately just
; assume term, we can ignore ttree.

   (cond
    ((ts= ts *ts-nil*)
     (mv :known-false
         (cons-tag-trees ttree tag-tree)))
    ((ts-disjointp ts *ts-nil*)
     (mv :known-true
         (cons-tag-trees ttree tag-tree)))
    (t (mv-let
        (forced tag-tree)
        (cond
         ((not force-flg)
          (mv nil tag-tree))
         (t
          (force-assumption 'equal target term type-alist nil
                            immediatep
                            force-flg tag-tree)))
        (cond
         ((not forced)

; Since we cannot determine that the proposed assumption is non-nil,
; but we are not allowed to force, we signal failure instead.

          (mv :failed tag-tree))
         (t (mv :added tag-tree))))))))

; Historical note on the evolution of type-alist-clause.

; Early on, we had a simple version of type-alist-clause that simply looped
; through the literals in the clause, calling assume-true-false for each one.
; With this approach, before we eliminated guards from the logic, the result
; could be very sensitive to the order of the literals in the clause.  Consider
; the following theorem, which was not proved before we made this change:

; (implies (and (< 1 (+ 1 n))
;               (< 0 n)
;               (integerp n))
;          (equal (< 1 (+ 1 n)) (< 0 n)))

; The problem with this theorem was that the first two hypotheses
; weren't known to be Boolean unless we knew (for example) the third
; hypothesis.  A more low-level example could be obtained by applying
; type-alist-clause to ((< n '0) (not (integerp n)) (equal n '0)), and
; then checking the type-set of n in the resulting type-alist.

; One possible solution was to order the clause heuristically on the
; way in to type-alist-clause.  One nice thing about that idea is that
; the clause is only rearranged locally, so the change will not be
; pervasive.  However, the completeness of this process is
; questionable since the process is not iterative.

; So our next idea, through Version 1.7, was to iterate, calling
; type-alist-clause repeatedly until the answer stabilizes.  Actually we were
; slightly more clever than that.  The main trick was that when we applied
; assume-true-false to a literal, we did so with the force-flg set so that we
; were allowed to generate assumptions.  Then we checked if any assumptions
; were generated as a result.  If so, we delayed consideration of that literal
; and all other such literals until there was no further delay possible.  Note:
; if force-flg was actually t, then no change was necessary.  All this was
; simply to handle the case that force-flg is nil.

; Here are more details on that earlier approach.

; Stage 1:  Repeat the following process:  Loop through all the
; literals, allowing forcing to take place, but if any assumptions are
; generated then delay consideration of that literal.  As long as at
; least one literal seems to contribute to the evolving type-alist in
; a given pass through the loop, we'll pass through the loop again.

; Stage 2:  We may now assume that none of the remaining literals has
; been processed, because they all cause splitting.  We now process
; them all with the force-flg off so that we can be sure that no
; assumptions are generated.

; Stage 3 (perhaps overkill):  Repeat stage 1, but this time give up
; when we make it all the way through the loop without success.

; Starting with Version 1.8, with guards eliminated from the logic, we saw
; no reason to be so clever.  So, we reverted once again to a more
; straightforward algorithm.

(defun return-type-alist
  (hitp car-type-alist rest-type-alist original-type-alist wrld)

; Hitp should be t or nil, not 'contradiction.  We simply return (cons
; car-type-alist rest-type-alist), except that if hitp is nil then we
; assume that this is equal to original-type-alist and save ourselves a cons.

  (if hitp
      (mv-let (ts ttree)
              (assoc-type-alist (car car-type-alist) rest-type-alist wrld)
              (let* ((ts (or ts *ts-unknown*))
                     (int (ts-intersection ts (cadr car-type-alist))))
                (cond
                 ((ts= int ts) rest-type-alist)
                 ((ts= int (cadr car-type-alist))
                  (extend-type-alist
                   (car car-type-alist)
                   (cadr car-type-alist)
                   (cddr car-type-alist)
                   rest-type-alist
                   wrld))
                 (t
                  (extend-type-alist
                   (car car-type-alist)
                   int
                   (cons-tag-trees ttree (cddr car-type-alist))
                   rest-type-alist
                   wrld)))))
      original-type-alist))

(defun type-alist-equality-loop1 (type-alist top-level-type-alist ens w)

; Return (mv hitp type-alist ttree), where hitp is 'contradiction, t (meaning
; "hit"), or nil.  If hitp is 'contradiction, then ttree explains why;
; otherwise, ttree is irrelevant.  We map down type-alist (which is initially
; the top-level-type-alist) and milk each (EQUAL arg1 arg2) assumed true on it
; by setting the types of arg1 and arg2 each to the intersection of their
; top-level types.  This same intersection process was performed when the
; EQUALity was assumed true, but we might have since learned more about the
; types of the two arguments.

  (cond
   ((null type-alist)
    (mv nil nil nil))
   (t
    (mv-let (hitp rest-type-alist rest-ttree)
        (type-alist-equality-loop1 (cdr type-alist) top-level-type-alist ens w)
      (cond
       ((eq hitp 'contradiction)
        (mv hitp rest-type-alist rest-ttree))
       ((and (ffn-symb-p (caar type-alist) 'equal)
             (ts= (cadar type-alist) *ts-t*))
        (let ((arg1 (fargn (caar type-alist) 1))
              (arg2 (fargn (caar type-alist) 2))
              (ttree0 (cddar type-alist)))

; The following code is very similar to code in the 'equal case in
; assume-true-false

          (mv-let
              (ts1 ttree)
              (type-set arg1 nil nil top-level-type-alist ens w nil nil nil)
            (mv-let
                (ts2 ttree)
                (type-set arg2 nil nil top-level-type-alist ens w ttree nil
                          nil)

; Observe that ttree records the dependencies of both args.

              (let ((int (ts-intersection ts1 ts2)))
                (cond
                 ((ts= int *ts-empty*)
                  (mv 'contradiction nil (puffert ttree)))
                 ((ts= ts1 ts2)
                  (mv hitp
                      (return-type-alist hitp (car type-alist)
                                         rest-type-alist type-alist w)
                      nil))
                 (t

; We return now with hitp = t.  But the returned type-alist could still equal
; the input type-alist, because when extend-with-proper/improper-cons-ts-tuple
; preserves the type-alist invariants, it can do so by refusing to extend
; type-alist.

                  (mv t
                      (let ((shared-ttree
                             (puffert (cons-tag-trees ttree0 ttree)))
                            (type-alist
                             (return-type-alist hitp (car type-alist)
                                                rest-type-alist type-alist w))
                            (backchain-limit (backchain-limit w :ts)))
                        (cond
                         ((ts= ts1 int)
                          (extend-with-proper/improper-cons-ts-tuple
                           arg2 int shared-ttree nil nil top-level-type-alist
                           nil ens type-alist w
                           nil nil backchain-limit))
                         ((ts= ts2 int)
                          (extend-with-proper/improper-cons-ts-tuple
                           arg1 int shared-ttree nil nil top-level-type-alist
                           nil ens type-alist w
                           nil nil backchain-limit))
                         (t
                          (extend-with-proper/improper-cons-ts-tuple
                           arg2 int shared-ttree nil nil top-level-type-alist
                           nil ens
                           (extend-with-proper/improper-cons-ts-tuple
                            arg1 int shared-ttree nil nil top-level-type-alist
                            nil ens type-alist w
                            nil nil backchain-limit)
                           w
                           nil nil backchain-limit))))
                      nil))))))))
       (t (mv hitp
              (return-type-alist
               hitp (car type-alist) rest-type-alist type-alist w)
              nil)))))))

(defun clean-up-alist (alist ans)

; Remove duplicate (mod equal) key entries from alist, accumulating the final
; answer onto ans (which is assumed to be nil initially).  We keep the first of
; each duplicate binding and thus we do not change the value of assoc-equal on
; the alist.  However, the order of the pairs in the returned alist is the
; reverse of that in the initial alist.

  (cond ((null alist) ans)
        ((assoc-equal (caar alist) ans)
         (clean-up-alist (cdr alist) ans))
        (t (clean-up-alist (cdr alist) (cons (car alist) ans)))))

(defun duplicate-keysp (alist)

; Determine whether there is a key bound twice (mod equal) in alist.  We return
; the first pair whose key is bound twice, so that we can extract the key from
; that pair in an error report if we like.  (We could return the car of the
; first pair, but if it were nil then we could not distinguish from the error
; case.)

  (cond ((null alist) nil)
        ((assoc-equal (caar alist) (cdr alist))
         (car alist))
        (t (duplicate-keysp (cdr alist)))))

(defun clean-type-alist (type-alist)

; We obtained a 12.4% decrease in the time for an example from Dave Greve, by
; avoiding the expense of duplicate-keysp in the commented code below.  In that
; example we found a type-alist with 234 members; thus, the speedup is the
; result of eliminating the quadratic behavior of duplicate-keysp and/or
; clean-up-alist (probably the former).  The regression suite did not slow down
; as a result of eliminating this "optimization", which presumably had been
; intended to keep the type-alist small by eliminating duplicate keys (though
; it seems quite possible that such duplication was infrequent).

; (if (duplicate-keysp type-alist)
;     (reverse (clean-up-alist type-alist nil))
;     type-alist))

  type-alist)

(defun type-alist-equality-loop-exit (type-alist)
  (er hard 'type-alist-equality-loop-exit
      "We're apparently in an infinite type-alist-equality-loop!  The ~
       offending type-alist is:~%~x0"
      type-alist))

(defconst *type-alist-equality-loop-max-depth* 10)

(defun type-alist-equality-loop (type-alist0 ens w n)

; Returns (mv contradictionp type-alist ttree), where type-alist has no
; duplicate keys and all the (EQUAL arg1 arg2) assumed true in it have been
; milked so that arg1 and arg2 have equal type-sets.

  (let ((type-alist (clean-type-alist type-alist0)))
    (mv-let (hitp type-alist ttree)
            (type-alist-equality-loop1 type-alist type-alist ens w)
            (cond
             ((eq hitp 'contradiction)
              (mv t nil ttree))
             ((= n 0)
              (if (or (not hitp)

; It is possible, even with hitp, for (equal type-alist type-alist0) to be
; true.  There is a comment to this effect, regarding type-alist invariants, in
; type-alist-equality-loop1.  We discovered this in Version_2.7 during
; regression tests, specifically, with the last form in the community book
; books/workshops/2000/manolios/pipeline/pipeline/deterministic-systems/128/top/ma128-isa128.
; This function was being called differently because of a change in in
; built-in-clausep to use forward-chaining.

                      (equal type-alist type-alist0))
                  (mv nil type-alist nil)
                (mv nil (type-alist-equality-loop-exit type-alist) nil)))
             (hitp
              (type-alist-equality-loop type-alist ens w (1- n)))
             (t
              (mv nil type-alist nil))))))

(defun put-assoc-equal-ts (term ts ttree type-alist)
  (declare (xargs :guard (alistp type-alist)))
  (cond ((endp type-alist) (list (list* term ts ttree)))
        ((equal term (caar type-alist))
         (let ((ts1 (ts-intersection ts (cadar type-alist))))
           (cond ((ts= ts1 (cadar type-alist))
                  type-alist)
                 (t (cons (list* term ts ttree)
                          (cdr type-alist))))))
        (t (cons (car type-alist)
                 (put-assoc-equal-ts term ts ttree (cdr type-alist))))))

(defun reconsider-type-alist (type-alist xtype-alist force-flg ens w pot-lst
                                         pt)

; We return (mv contradictionp xtype-alist' ttree) where either contradictionp
; is t and ttree explains, or else those two are nil and xtype-alist' is a
; strengthening of xtype-alist obtained by retyping every term in it, under
; type-alist, using double whammy.

; Through Version_4.1, we accumulated an argument, seen, that accumulated keys
; of type-alist in order to avoid considering a key more than once.  However,
; the apparent gain can be offset by the quadratic nature of a corresponding
; test, (member-equal (caar type-alist) seen).  Indeed, we decreased the time
; by 13.7% in our preliminary removal of "seen", in an example from Dave Greve,
; without noticeable impact on the regression suite.

  (cond ((null type-alist)
         (mv nil xtype-alist nil))
        ((ffn-symb-p (caar type-alist) 'IF)

; Through Version_2.5 we retyped IF expressions.  But with the introduction
; of assume-true-false-if it became both prohibitively expensive and
; practically unnecessary.   So we don't do it anymore.

         (reconsider-type-alist (cdr type-alist)
                                xtype-alist force-flg ens w pot-lst pt))
        (t
         (mv-let (ts ttree)
                 (type-set (caar type-alist)
                           force-flg
                           (cons :SKIP-LOOKUP

; See type-set-rec for a discussion of :SKIP-LOOKUP.  Warning: Do not change
; this car to another value without seeing the warning in recognizer-tuple.

                                 (cdar type-alist))
                           xtype-alist ens w nil pot-lst
                           pt)

; We are looking at a triple (term1 ts1 . ttree1).  So we obtain the type-set
; of term1, ts, using the double whammy.  That guarantees to intersect ts1 with
; the directly computed type-set of term1 and to cons together ttree1 and the
; directly computed ttree.  Proof: type-set will see this very triple (because
; seen ensures this is the first such one) and type-set-finish always conses in
; the old ttree.

; If ts is empty then a contradiction has been detected.  If ts is the same as
; ts1 we haven't learned anything and don't waste time and space adding the
; "new" binding of term1.

                 (cond
                  ((ts= ts *ts-empty*) (mv t nil ttree))
                  (t (reconsider-type-alist
                      (cdr type-alist)
                      (cond ((ts-subsetp (cadar type-alist) ts)
                             xtype-alist)
                            (t
                             (put-assoc-equal-ts (caar type-alist)
                                                 ts ttree xtype-alist)))
                      force-flg ens w pot-lst pt)))))))

(defun type-alist-clause-finish1 (lits ttree-lst force-flg type-alist ens wrld)

; Assume the falsity of every literal in lits, extending type-alist.  Return
; (mv contradictionp type-alist' ttree), where either contradictionp is t and
; ttree explains the contradiction or else those two results are nil and
; type-alist' is an extension of type-alist.

; This function is very sensitive to the order in which the literals are
; presented.  For example, if lits is ((rationalp (binary-+ '1 i)) (not
; (integerp i))) you will get back a type-alist in which (binary-+ '1 i) is
; assumed non-rational but i is assumed integral.  If the two literals are
; reversed you will get back the contradiction signal because if i is known
; integral then (binary-+ '1 i) is known integral.  It is the role of
; reconsider-type-alist to improve the first case.

  (cond ((null lits) (mv nil type-alist nil))
        (t (mv-let
            (mbt mbf tta fta ttree)
            (assume-true-false (car lits)
                               (car ttree-lst)
                               force-flg
                               nil
                               type-alist
                               ens
                               wrld
                               nil nil :tta)
            (declare (ignore tta))
            (cond
             (mbt (mv t nil ttree))
             (mbf (type-alist-clause-finish1 (cdr lits) (cdr ttree-lst)
                                            force-flg
                                            type-alist ens wrld))
             (t (type-alist-clause-finish1 (cdr lits) (cdr ttree-lst)
                                           force-flg
                                           fta ens wrld)))))))

(defun type-alist-clause-finish (lits ttree-lst force-flg type-alist ens wrld
                                 pot-lst pt)

; Assume the falsity of every literal in lits, extending type-alist.  Return
; (mv contradictionp type-alist' ttree), where either contradictionp is t and
; ttree explains the contradiction or else those two results are nil and
; type-alist' is an extension of type-alist.  This function is not as sensitive
; to order as the "single pass" version, type-alist-clause-finish1, because we
; reconsider the resulting type-alist and try to strengthen each type with a
; double whammy type-set.

  (mv-let (contradictionp type-alist ttree)
    (type-alist-clause-finish1 lits ttree-lst
                               force-flg type-alist ens wrld)
    (cond (contradictionp
           (mv contradictionp type-alist ttree))
          (t
           (mv-let (contradictionp new-type-alist ttree)
             (reconsider-type-alist type-alist type-alist
                                    force-flg ens wrld pot-lst pt)
             (cond (contradictionp
                    (mv contradictionp new-type-alist ttree))
                   ((or (equal new-type-alist type-alist)
                        (null pot-lst))
                    (mv contradictionp new-type-alist ttree))

; As of v2-8, we reconsider-type-alist a second time if reconsidering
; once changed the type-alist and the pot-lst is not empty.  When we
; first constructed the type-alist, we did not use the pot-lst.  Thus,
; this second call to reconsider-type-alist performs much the same
; purpose relative to the pot-lst that the first (and originally, only)
; call plays with respect to the type-alist.  This type of heuristic
; is intimately tied up with the treatment of the DWP flag.

                   (t
                    (reconsider-type-alist new-type-alist new-type-alist
                                           force-flg ens wrld pot-lst
                                           pt))))))))

; Essay on Repetitive Typing

; Suppose you are asked to assume (not (integerp (1+ i))) and then are asked to
; assume (integerp i).  This might happen if you are building a type-alist for
; a sequence of literals and the literals appear in the order presented above.
; When it happens in that way, it is handled by type-alist-clause.  We have
; tried a variety of solutions to this problem, named and sketched below.

; naive: don't do anything.  The system will fail to note the contradiction
;  above.  This has actually burned Bishop in "real" theorems.

; force-based iteration in type-alist-clause: In Version 1.7 we had an
;  iteration scheme in type-alist-clause based on the fact that (in that
;  version of the system) (1+ i) forced the hyp that i is a number and, by
;  noting the attempted force and skipping the literal, we delayed the
;  processing of the first literal until we had processed the others.  But when
;  Version 1.8 came along and forcing became much less common, this approach
;  was removed and (without much thought) we reverted back to the naive
;  approach and burned Bishop.

; repetitious assume-true-false: The first fix to the situation just described
;  was to define a new version of assume-true-false, called
;  repetitious-assume-true-false, which noted when it added a pair on the
;  type-alist that bound a term which occurred as a proper subterm of some
;  previously bound term.  Thus, when (integerp i) was assumed in the context
;  of (not (integerp (1+ i))), the binding of i provoked
;  repetitious-assume-true-false to recompute the type of the previously bound
;  (1+ i).  To do this, repetitious-assume-true-false had to insist that the
;  recomputation use the "double whammy" idea (so as not to be fooled into just
;  looking up the previously assumed type) and we added the "dwp" flag to the
;  type-set clique.  Repetitious-assume-true-false was used in place of
;  assume-true-false everywhere in the code from rewrite.lisp onwards (i.e.,
;  type-set still used assume-true-false, as did normalize and
;  distribute-first-if).  Note that this is more general than an attack at the
;  type-alist-clause level because it affects any assumption, not just those
;  made at the clause level.  But we found this inefficient and have abandoned
;  it.

; reconsider-type-alist (1): As an alternative to the repetitious
;  assume-true-false, we reverted to the idea of working at the
;  type-alist-clause level, but basing the iteration on something besides
;  forcing.  The idea was to do a simple assume-true-false on each literal of
;  the clause (taking the false type-alist always) and then to reconsider the
;  final type-alist by computing the type of each bound term (with dwp) in the
;  context of the final type-alist.  Observe that we only make one
;  reconsideration pass.  As of this writing (Feb 10, 1995) Version 1.8 uses
;  this style of type-alist-clause.

; Here are some performance measures.

; The simplest example is one which fails unless we do some kind of iterated
; typing.  Here is Bishop's example:

; (thm (IMPLIES (AND (< 0 (+ (- I) N))
;                    (NOT (INTEGERP (+ (- I) N)))
;                    (INTEGERP N)
;                    (INTEGERP I)
;                    )
;               nil))

; The naive method fails to prove this.  Force-based iteration catches it if (-
; I) forces something, but that is not the case in Version 1.8 and so that kind
; of iteration doesn't prove this.  The other two iterative schemes do catch
; it.  In experimenting though be sure to notice whether it is proved by
; type-alist-clause or something more expensive such as linear arithmetic.

; A good performance test is

; (defthm ordered-symbol-alistp-remove1-assoc-eq-test
;   (implies (and (ordered-symbol-alistp l)
;                 (symbolp key)
;                 (assoc-eq key l))
;            (ordered-symbol-alistp (remove1-assoc-eq key l)))
;   :hints (("Goal" :in-theory
;            (disable ordered-symbol-alistp-remove1-assoc-eq))))

; The naive approach does this in about 3.4 seconds (prove time, on Rana, a
; Sparc 2).  The repetitious approach takes 5.6 seconds.  The reconsidering
; approach takes 3.6.  Analysis of the repetitious data show that in this
; example repetitious-assume-true-false is called 5606 times but the repetition
; changes the type-alist only 92 times.  When it does change, the newly bound
; subterm was a variable symbol 80% of the 92 times.  and it was (CAR var) or
; (CDR var) in the remaining 20%.  The low hit rate of the repetitious
; assume-true-false encouraged us to reconsider the idea.

; But the following test convinced us that repetitious assume-true-false is
; doomed.  Consider processing the Nqthm package proofs.  The naive approach
; took about 1683 seconds.  The repetitious approach never completed.  See the
; comment in REWRITE-IF about repetitious-assume-true-false for an explanation.
; The reconsidering approach took 1654 seconds.  Only six events had times more
; than 1 second greater than in the naive approach (and overall, it is about 30
; seconds faster).

(defun type-alist-clause (cl ttree-lst force-flg type-alist ens wrld
                          pot-lst pt)

; We construct an extension of type-alist in which every literal of cl is
; assumed false.  Ttree-lst is a list of ttrees in (weak) 1:1 correspondence
; with cl.  The 'pt tags in the tree corresponding to a given literal indicates
; the parents of that literal.  (By "weak" we allow ttree-lst to be shorter
; than cl and for all "excess literals" of cl to have the nil ttree, i.e., we
; just cdr ttree-lst as we go through cl and use car of the car as a (possibly
; nil) ttree whenever we need a ttree.)  We return three values.  The first is
; t or nil and indicates whether we found a contradiction, i.e., that some
; literal of cl is true.  The second is the resulting type-alist (or nil if we
; got a contradiction).  The third is a ttree explaining the contradiction (or
; nil if we got no contradiction).  The type-alist entries generated for a
; given literal contain the corresponding ttree from ttree-lst.

; Warning: It is probably silly to call this function with force-flg =
; t except for heuristic use, e.g., to see what the probable types of
; some terms are.  The reason is that since we process the lits of cl
; one at a time, we may well add 'assumptions that are in fact denied
; by later literals, causing loops because the case split generates
; the original clause again.  If called with force-flg = t, then the
; type-alist we generate may have 'assumptions in it.  This type-alist
; must be handled with care so that if those assumptions are raised
; the necessary case splits are done.

; Note: Because force-flg can make provisionally false terms look like
; false terms, we sometimes appear simply to have dropped a literal of
; cl.  For example, consider the clause {...(not (acl2-numberp
; (binary-+ x y))) ...}.  Because of force-flg, that literal looks
; false, i.e., binary-+ "always" returns an acl2-numberp.  Assuming
; the literal raises the 'assumptions that x and y are both
; acl2-numberps but sets mbf below to t.  We therefore skip the
; literal, ignoring also its 'assumptions.  If we look at the clause
; as a formula: (implies (and ... (acl2-numberp (+ x y)) ...) ...)
; and imagine ourselves working on the conclusion, it is as though we
; have simply dropped the hypothesis.  This is sound.  More generally,
; we can throw away any pair from a type-alist.  But this is an
; acceptable thing to do here because, first, (acl2-numberp (+ x y))
; tells us nothing about x and y -- they may both be orange trees for
; all we know.  Second (pretending that we are in a pre-1.8 version of
; ACL2, in which the guard for + was part of its defining axiom), if (+ x y)
; occurs in the conjecture anywhere we will assume it is numeric anyway and
; deal with the 'assumptions that its args are acl2-numberps.  So in some
; sense, a hypothesis like (acl2-numberp (+ x y)) is irrelevant because it is
; always given and we pay for it only when it helps us.

  (if force-flg
      (type-alist-clause-finish cl ttree-lst force-flg type-alist ens wrld
                                pot-lst pt)
      (mv-let (contradictionp type-alist0 ttree0)
              (type-alist-clause-finish cl ttree-lst nil
                                        type-alist ens wrld
                                        pot-lst pt)
              (cond
               (contradictionp
                (mv t nil ttree0))
               (t
                (type-alist-equality-loop
                 type-alist0 ens wrld
                 *type-alist-equality-loop-max-depth*))))))

(defun known-whether-nil (x type-alist ens force-flg dwp wrld ttree)

; This function determines whether we know, from type-set reasoning, whether x
; is nil or not.  It returns three values.  The first is the answer to the
; question "Do we know whether x is nil or not?"  If the answer to that
; question is yes, the second value is the answer to the question "Is x nil?"
; and the third value is a ttree that extends the input ttree and records the
; 'assumptions and dependencies of our derivation.  If the answer to the first
; question is no, the second value is nil, and the third is the input ttree
; (thus, this function is a No-Change Loser).  Note that this function may
; generate 'assumptions and so splitting has to be considered.

  (cond ((quotep x)
         (mv t (equal x *nil*) ttree))
        (t (mv-let (ts ttree1)
             (type-set x force-flg dwp type-alist ens wrld ttree nil nil)
             (cond ((ts= ts *ts-nil*)
                    (mv t t ttree1))
                   ((ts-intersectp ts *ts-nil*)
                    (mv nil nil ttree))
                   (t (mv t nil ttree1)))))))

(defun ts-booleanp (term ens wrld)
  (mv-let (ts ttree)
          (type-set term nil nil nil ens wrld nil nil nil)
          (cond ((tagged-objectsp 'assumption ttree)
                 (er hard 'ts-booleanp
                     "It was thought impossible for a call of type-set with ~
                      force-flg = nil to produce an 'assumption, but ~
                      ts-booleanp did it on ~x0."
                     term))
                (t (ts-subsetp ts *ts-boolean*)))))

(defun weak-cons-occur (x y)

; Both x and y are terms.  In addition, x is known to be non-quoted
; and not a CONS expression.  Consider the binary tree obtained by
; viewing the term y as a CONS tree.  We return t iff x is a tip of
; that tree.

  (cond ((variablep y) (eq x y))
        ((fquotep y) nil)
        ((eq (ffn-symb y) 'cons)
         (or (weak-cons-occur x (fargn y 1))
             (weak-cons-occur x (fargn y 2))))
        (t (equal x y))))

(defun equal-x-cons-x-yp (lhs rhs)

; We answer the question ``Is (EQUAL lhs rhs) definitely nil?''  If
; our result is t, then the equality is definitely nil, without
; further qualification.  If we say we don't know, i.e., nil, nothing
; is claimed.

; However, we know some things about lhs and rhs that allow us to
; make this function answer ``I don't know'' more quickly and more
; often than it might otherwise.  We assume that lhs and rhs are not
; identical terms and we know they are not both quoted constants
; (though either may be) and we know that their type sets have a
; non-empty intersection.

; We make our positive decision based on structural reasoning.  For
; example, (EQUAL x (CONS x &)), is NIL because x occurs properly
; within the CONS tree.  This observation does not depend on type-sets or
; anything else.

; However, we don't want to do too much work exploring the two terms.
; For example, if they are both large explicit values we don't want to
; look for them in each other.  We know that we will eventually apply
; the CONS-EQUAL axiom, which will rewrite the equality of two conses
; (constants or otherwise) to the conjoined equalities of their
; components.  Thus, if both lhs and rhs are CONS expressions (i.e., a
; consityp) or quoted list constants, we just return nil and let the
; :REWRITE rules take care of it.

; One more minor optimization: if one of our args is a consityp and
; the other is a quoted constant then the constant must be a consp or
; else the type sets wouldn't intersect.

; Further Work:

; If this function is improved, also consider similar improvements to
; almost-quotep, which, like this function, currently only works on
; cons terms but could be generalized.

; This function has an arithmetic analog.  For example:
;    (EQUAL x (+ a (+ b (+ x c))))
; is NIL if x has type set *ts-acl2-number* and the type set of the
; sum of the other addends, (+ a (+ b c)), does not intersect *ts-zero*.
; We will eventually add :REWRITE rules to normalize + and do cancellation.
; That will make it easier to find x and may in fact subsume the kind of
; reasoning done here.  On the other hand, heuristically it is probably
; good to put every ounce of knowledge we have about these elementary
; things every place we can.

; Similarly, (EQUAL x (* a (* b (* x c)))), is false if x is a non-*ts-zero*
; *ts-acl2-number* and (* a (* b c)) is a non-*ts-integer*.

; Similarly, (EQUAL x (- x)) is nil if x is a non-*ts-zero* *ts-acl2-number*.

; Similarly, (EQUAL x (/ x)) is nil if x is a non-*ts-zero* *ts-ratio*
; or a *ts-complex-rational*.

  (cond ((variablep lhs)
         (cond ((consityp rhs)
                (or (weak-cons-occur lhs (fargn rhs 1))
                    (weak-cons-occur lhs (fargn rhs 2))))
               (t nil)))
        ((fquotep lhs) nil)
        ((eq (ffn-symb lhs) 'cons)
         (cond ((variablep rhs)
                (or (weak-cons-occur rhs (fargn lhs 1))
                    (weak-cons-occur rhs (fargn lhs 2))))
               ((fquotep rhs) nil)
               ((eq (ffn-symb rhs) 'cons) nil)
               (t (or (weak-cons-occur rhs (fargn lhs 1))
                      (weak-cons-occur rhs (fargn lhs 2))))))
        ((consityp rhs)
         (or (weak-cons-occur lhs (fargn rhs 1))
             (weak-cons-occur lhs (fargn rhs 2))))
        (t nil)))

(defun not-ident (term1 term2 type-alist ens wrld)

; We return two results.  The first is t iff (equal term1 term2) is
; false.  The second is a ttree that justifies the answer.  If the
; first result is nil, so is the second.  This function does not
; generate 'assumptions, so it is "weak."  I.e., it will not decide
; (equal (+ x y) (cons x y)) unless x and y are both acl2-numberps; one
; might have expected it to say the equality is false and to raise the
; assumptions that x and y are acl2-numberps.  The only place this function
; is used, presently, is in normalization, which does not raise
; assumptions.

  (cond ((and (quotep term1)
              (quotep term2))
         (mv (not (equal term1 term2)) nil))
        (t (mv-let (ts1 ttree)
                   (type-set term1 nil nil type-alist ens wrld nil nil nil)
                   (mv-let (ts2 ttree)
                           (type-set term2 nil nil type-alist ens wrld ttree
                                     nil nil)
                           (cond
                            ((ts-disjointp ts1 ts2)
                             (mv t ttree))
                            ((equal-x-cons-x-yp term1 term2)

; Observe that we claim term1 is not term2 without any dependency on
; the type-set ttrees.  Even though the heuristic reasonableness of
; equal-x-cons-x-yp depends on the two having intersecting type-sets
; (otherwise, equal-x-cons-x-yp could do a little more work and decide
; the question), the correctness of its positive answer doesn't depend
; on anything.

                             (mv t nil))
                            (t (mv nil nil))))))))

(defun first-if (args i)

; This function searches the top level of the list args for an
; top-level IF expression.  If it does not find one, it returns
; 2 nils.  Otherwise, it returns the position of the first one
; it finds and the IF expression found.

  (cond ((null args) (mv nil nil))
        ((ffn-symb-p (car args) 'if)
         (mv i (car args)))
        (t (first-if (cdr args) (1+ i)))))

(defun all-variablep (lst)
  (cond ((null lst) t)
        (t (and (variablep (car lst))
                (all-variablep (cdr lst))))))

(defun normalize-with-type-set (term iff-flg type-alist ens wrld ttree
                                     ts-backchain-limit)

; The args to this function are as in normalize, below.  We return a
; term and a ttree.  The term is equivalent (mod iff-flg and
; type-alist) to term.  We base our answer on type-set reasoning
; alone.  No 'assumptions are generated.

  (mv-let
   (ts new-ttree)
   (type-set-bc term nil nil type-alist ens wrld ttree nil nil
                ts-backchain-limit)
   (let ((new-term
          (cond ((ts-intersectp ts *ts-nil*)
                 (cond
                  ((ts= ts *ts-nil*) *nil*)
                  (t term)))
                (iff-flg *t*)
                ((ts= ts *ts-t*) *t*)
                ((ts= ts *ts-zero*) *0*)
                ((ts= ts *ts-one*) *1*)
                (t term))))
     (mv new-term
         (if (equal term new-term) ttree new-ttree)))))

(mutual-recursion

; Note: The following function does not normalize IFs that occur in
; lambda arguments.  I once tried ``fixing'' that oversight and found
; that it cost a lot on big lambda examples in the Rockwell suite.

; NOTE: Type-set and assume-true-false must be called with force-flg = nil,
; since normalize can recur on a lambda-body whose variables are not the
; variables of the top-level environment.

(defun normalize (term iff-flg type-alist ens wrld ttree ts-backchain-limit)

; This function normalizes the if structure of term, simplifying with
; type-set reasoning as it goes.  We return two results, a term and a
; ttree.  The term is equivalent to term (propositionally equivalent,
; if the iff-flg is t) under the assumptions in type-alist.  No
; 'assumption tags are generated.  The ttree records the lemmas we
; used as recovered from the type-alist and elsewhere and is an
; extension of the input ttree.

; We expand some calls of members of
; *expandable-boot-strap-non-rec-fns* as we go.

; This function combines three more or less separate ideas: if
; normalization, expanding boot-strap non-rec fns, and simplifying
; with type-set information.  The reason we do all at once is to
; prevent explosions that would occur if we did them individually.

  (cond
   ((variablep term)
    (normalize-with-type-set term iff-flg type-alist ens wrld ttree
                             ts-backchain-limit))
   ((fquotep term)
    (mv (cond ((and iff-flg (not (equal term *nil*))) *t*)
              (t term))
        ttree))
   ((flambda-applicationp term)
    (mv-let (normal-args ttree)
      (normalize-lst (fargs term) nil
                     type-alist ens wrld ttree
                     ts-backchain-limit)

; We normalize the body of the lambda (under a type-alist determined
; from the normalized arguments).  But we leave a lambda application
; in place.

      (mv-let (normal-body ttree)
        (normalize (lambda-body (ffn-symb term))
                   iff-flg
                   (zip-variable-type-alist
                    (lambda-formals (ffn-symb term))
                    (type-set-lst
                     normal-args
                     nil ; see note above on force-flg
                     nil
                     type-alist
                     nil
                     ens
                     wrld
                     nil nil
                     ts-backchain-limit))
                   ens wrld ttree ts-backchain-limit)
        (mv (mcons-term
             (list 'lambda
                   (lambda-formals (ffn-symb term))
                   normal-body)
             normal-args)
            ttree))))
   ((eq (ffn-symb term) 'if)
    (mv-let
      (t1 ttree)
      (normalize (fargn term 1) t type-alist ens wrld ttree ts-backchain-limit)
      (let ((t2 (fargn term 2))
            (t3 (fargn term 3)))
        (mv-let
          (mbt mbf tta fta ttree1)
          (assume-true-false-bc t1 nil
                                nil ; see note above on force-flg
                                nil type-alist ens wrld nil nil nil
                                ts-backchain-limit)
          (cond
           (mbt (normalize t2 iff-flg type-alist ens wrld
                           (cons-tag-trees ttree1 ttree)
                           ts-backchain-limit))
           (mbf (normalize t3 iff-flg type-alist ens wrld
                           (cons-tag-trees ttree1 ttree)
                           ts-backchain-limit))

; If mbt and mbf are both nil, then ttree1 is nil and we ignore it
; below.  (Actually, we use the same variable name to hold a different
; ttree.)

           ((ffn-symb-p t1 'if)
            (let ((t11 (fargn t1 1))
                  (t12 (fargn t1 2))
                  (t13 (fargn t1 3)))
              (normalize (mcons-term* 'if t11
                                      (mcons-term* 'if t12 t2 t3)
                                      (mcons-term* 'if t13 t2 t3))
                         iff-flg type-alist ens wrld ttree ts-backchain-limit)))
           (t (mv-let (t2 ttree)
                (normalize t2 iff-flg tta ens wrld ttree ts-backchain-limit)
                (mv-let (t3 ttree)
                  (normalize t3 iff-flg fta ens wrld ttree
                             ts-backchain-limit)
                  (cond ((equal t2 t3)
                         (mv t2 ttree))
                        ((and (equal t1 t2)
                              (equal t3 *nil*))
                         (mv t1 ttree))
                        ((and (equal t2 *t*)
                              (equal t3 *nil*))

; If t1 is Boolean and t2 and t3 are t and nil respectively, we can normalize
; to t1.  Similarly, if t1 is not Boolean but we are working in iff-mode,
; we can normalize to t1.  At one time, we handled the iff-flg case separately
; and generalized the (equal t2 *t*) test to known-whether-nil.  That is
; unnecessary.  If iff-flg is set then t2 will have been normalized in iff
; mode.  Thus, if it is non-nilp t2 would be *t*.

                         (cond
                          (iff-flg (mv t1 ttree))
                          (t
                           (mv-let (ts1 ttree1)
                             (type-set-bc
                              t1 ; see note above on force-flg
                              nil nil type-alist ens wrld nil
                              nil nil
                              ts-backchain-limit)
                             (cond
                              ((ts-subsetp ts1 *ts-boolean*)
                               (mv t1 (cons-tag-trees ttree1
                                                      ttree)))
                              (t (mv (mcons-term* 'if t1 t2 t3)
                                     ttree)))))))
                        (t (mv (mcons-term* 'if t1 t2 t3)
                               ttree)))))))))))
   ((eq (ffn-symb term) 'hide)
    (mv term ttree))
   (t
    (mv-let (normal-args ttree)
      (normalize-lst (fargs term) nil
                     type-alist ens wrld ttree ts-backchain-limit)
      (let ((term (cons-term (ffn-symb term)
                             normal-args)))
        (cond
         ((fquotep term) (mv term ttree))
         ((eq (ffn-symb term) 'equal)
          (cond ((equal (fargn term 1) (fargn term 2))
                 (mv *t* ttree))
                (t (mv-let (not-ident ttree1)
                     (not-ident (fargn term 1)
                                (fargn term 2)
                                type-alist ens wrld)
                     (cond (not-ident (mv *nil*
                                          (cons-tag-trees ttree1
                                                          ttree)))
                           (t (distribute-first-if
                               term iff-flg
                               type-alist ens
                               wrld
                               ttree
                               ts-backchain-limit)))))))
         (t (distribute-first-if term iff-flg type-alist ens wrld
                                 ttree ts-backchain-limit))))))))

(defun normalize-lst (args iff-flg type-alist ens wrld ttree
                           ts-backchain-limit)
  (cond ((null args) (mv nil ttree))
        (t (mv-let (normal-arg ttree)
                   (normalize (car args) iff-flg type-alist ens wrld ttree
                              ts-backchain-limit)
                   (mv-let (normal-args ttree)
                           (normalize-lst (cdr args) iff-flg type-alist ens
                                          wrld ttree ts-backchain-limit)
                           (mv (cons normal-arg normal-args) ttree))))))

(defun normalize-or-distribute-first-if (term iff-flg type-alist ens wrld
                                              ttree ts-backchain-limit)
  (cond
   ((or (variablep term)
        (fquotep term))
    (normalize term iff-flg type-alist ens wrld ttree ts-backchain-limit))
   ((eq (ffn-symb term) 'equal)
    (cond ((equal (fargn term 1) (fargn term 2))
           (mv *t* ttree))
          (t (mv-let (not-ident ttree1)
                     (not-ident (fargn term 1) (fargn term 2) type-alist ens
                                wrld)
                     (cond (not-ident (mv *nil* (cons-tag-trees ttree1 ttree)))
                           (t (distribute-first-if term iff-flg type-alist ens
                                                   wrld ttree
                                                   ts-backchain-limit)))))))
   (t
    (distribute-first-if term iff-flg type-alist ens wrld ttree
                         ts-backchain-limit))))

(defun distribute-first-if (term iff-flg type-alist ens wrld ttree
                                 ts-backchain-limit)

; Term is known to be a non-variable non-quotep term in which all the
; args are in normal form.  We look for an if among its arguments and
; distribute the first one we find over the function symbol of term.
; In addition, this is the "bottoming out" code for normalize, at
; which we do anything else that is always done to non-IF terms.  In
; particular, we consider expanding certain non-rec fns.

; Rockwell Addition: We will get rid of certain functions like THE and
; HARD-ERROR in terms being processed by the theorem prover.  See
; remove-guard-holders and the Essay on the Removal of Guard Holders before it.
; That code will eliminate prog2$ (more accurately and more generally,
; return-last) from terms before normalize ever sees it.  So I dropped the
; first case of the old code here.

  (mv-let (n if-expr)
          (first-if (fargs term) 0)
          (cond
           ((null n)

; There is no if at the top-level of term, and since all the args are
; normalized, we know there are no ifs at all.  We are thus at the
; bottom of the IF tree and type-alist has on it everything we know.

            (cond
             ((member-eq (ffn-symb term)
                         *expandable-boot-strap-non-rec-fns*)
              (normalize
               (subcor-var (formals (ffn-symb term) wrld)
                           (fargs term)
                           (bbody (ffn-symb term)))
               iff-flg type-alist ens wrld ttree ts-backchain-limit))
             (t

; In this case the fn isn't expandable.  So we just take advantage of
; whatever type info we have and quit.

              (normalize-with-type-set term iff-flg
                                       type-alist ens wrld ttree
                                       ts-backchain-limit))))

; And here is the code after which this function was named.  We have
; found an if-expr in the args of term at location n.  Since that if
; is in normal form, its test is not an if.  We split on that test and
; distribute the if.

; Note: In nqthm, instead of using subst-for-nth-arg as below, we used
; subst-expr and hence hit not only the top-level occurrence of the
; bad if but every occurrence of it in the term.  This seems better
; because it doesn't search the term for (unlikely) occurrences and
; doesn't cons up a copy of the term.  However, if proofs don't work,
; reconsider this decision.

           (t (let ((t1 (fargn if-expr 1)))
                (mv-let
                 (mbt mbf tta fta ttree1)
                 (assume-true-false-bc t1 nil
                                       nil ; see note above on force-flg
                                       nil type-alist ens wrld nil nil nil
                                       ts-backchain-limit)
                 (cond
                  (mbt
                   (normalize-or-distribute-first-if
                    (cons-term (ffn-symb term)
                               (subst-for-nth-arg (fargn if-expr 2)
                                                  n
                                                  (fargs term)))
                    iff-flg type-alist ens wrld
                    (cons-tag-trees ttree1 ttree)
                    ts-backchain-limit))
                  (mbf
                   (normalize-or-distribute-first-if
                    (cons-term (ffn-symb term)
                               (subst-for-nth-arg (fargn if-expr 3)
                                                  n
                                                  (fargs term)))
                    iff-flg type-alist ens wrld
                    (cons-tag-trees ttree1 ttree)
                    ts-backchain-limit))
                  (t
                   (mv-let
                    (t2 ttree)
                    (normalize-or-distribute-first-if
                     (cons-term (ffn-symb term)
                                (subst-for-nth-arg
                                 (fargn if-expr 2)
                                 n
                                 (fargs term)))
                     iff-flg tta ens wrld ttree ts-backchain-limit)
                    (mv-let
                     (t3 ttree)
                     (normalize-or-distribute-first-if
                      (cons-term (ffn-symb term)
                                 (subst-for-nth-arg
                                  (fargn if-expr 3)
                                  n
                                  (fargs term)))
                      iff-flg fta ens wrld ttree ts-backchain-limit)
                     (cond ((equal t2 t3) (mv t2 ttree))
                           ((and (equal t1 t2)
                                 (equal t3 *nil*))
                            (mv t1 ttree))
                           ((and (equal t2 *t*)
                                 (equal t3 *nil*))
                            (cond
                             (iff-flg (mv t1 ttree))
                             (t (mv-let
                                 (ts1 ttree1)
                                 (type-set-bc t1 nil nil type-alist ens wrld
                                              nil nil nil ts-backchain-limit)
                                 (cond
                                  ((ts-subsetp ts1 *ts-boolean*)
                                   (mv t1 (cons-tag-trees ttree1 ttree)))
                                  (t (mv (mcons-term* 'if t1 t2 t3) ttree)))))))
                           (t (mv (mcons-term* 'if t1 t2 t3)
                                  ttree)))))))))))))

)

; The following functions are used only for debugging purposes.

(defun decode-type-set1 (ts alist)
  (cond ((ts= ts *ts-empty*) nil)
        ((null alist) (list ts))
        ((ts-subsetp (cdar alist) ts)
         (cons (caar alist)
               (decode-type-set1 (ts-intersection ts
                                                  (ts-complement (cdar alist)))
                                 (cdr alist))))
        (t (decode-type-set1 ts (cdr alist)))))

(defun decode-type-set (ts)

; This function converts a type-set into an untranslated term in the ACL2
; coding world.  For example, 1536 is converted into *TS-CONS* (which is the
; (TS-UNION *TS-PROPER-CONS* *TS-IMPROPER-CONS*)).  We do this only so that we
; can look at computed type-sets symbolically.

  (cond ((ts= ts *ts-unknown*) '*ts-unknown*)
        ((ts= ts *ts-empty*) '*ts-empty*)
        ((ts-complementp ts)
         (list 'ts-complement
               (decode-type-set (ts-complement ts))))
        (t (let ((lst (decode-type-set1
                       ts
                       *code-type-set-alist*)))
             (cond ((null (cdr lst)) (car lst))
                   (t (cons 'ts-union lst)))))))

(defmacro dts (term type-alist)

; A typical interaction with this macro is:

; ACL2 |>(dts '(denominator x) (list (cons 'x *ts-rational*)))
; (mv *TS-POSITIVE-INTEGER* ttree)

  `(mv-let (ts ttree)
           (type-set ,term nil nil ,type-alist
                     (ens state)
                     (w state)
                     nil nil nil)
           (mv (decode-type-set ts) ttree)))

; It is convenient to be able to get your hands on the global enabled
; structure for testing fns that take an ens arg:

(defun ens (state)
  (declare (xargs :guard (and (state-p state)
                              (f-boundp-global 'global-enabled-structure state))))
  (f-get-global 'global-enabled-structure state))
