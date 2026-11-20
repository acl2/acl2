; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "scripts")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mixed-script-detection
  :parents (unicode)
  :short "The scripts that a string can be written in,
          and whether there is any."
  :long
  (xdoc::topstring
   (xdoc::p
    "A string that mixes the letters of several scripts,
     such as Latin and Cyrillic, is a way to deceive a reader,
     because many letters of one script look like letters of another.
     Unicode Security Mechanisms [UTS #39, Section 5.1]
     defines when a string is mixed-script.
     The definition starts from
     the @('Script_Extensions') property (see @(see scripts)),
     which gives to each character the set of the scripts
     that the character is used with, and has three steps.")
   (xdoc::ol
    (xdoc::li
     "The augmented script set of a character
      is its @('Script_Extensions'), with two changes.
      A set that contains @('Common') or @('Inherited')
      is replaced by the set of all scripts, written ALL:
      a digit or a combining accent goes with every script.
      And to the other sets are added
      the writing systems that use several scripts
      and that have a script of the set among their scripts:
      see @(tsee writing-system).")
    (xdoc::li
     "The resolved script set of a string
      is the intersection of the augmented script sets of its characters.")
    (xdoc::li
     "A string is mixed-script if its resolved script set is empty,
      and single-script if it is not empty."))
   (xdoc::p
    "A single-script string need not be in one script only:
     its resolved script set can have several elements.
     And a string of digits is single-script:
     its resolved script set is ALL.")
   (xdoc::p
    "The definition changed in the revision of the specification
     that goes with Unicode 18.0.0,
     which added the writing system @('Hntl')
     (traditional Han with Latin).
     So the augmented script set of a character
     depends on the version of Unicode in two ways:
     through the @('Script_Extensions') of the character,
     and through this rule."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum writing-system
  :short "Fixtype of the elements of the sets of scripts
          that mixed-script detection uses."
  :long
  (xdoc::topstring
   (xdoc::p
    "An element is a script, that is,
     a value of the @('Script') property (see @(tsee script)),
     or one of four writing systems that use several scripts
     [UTS #39, Section 5.1].
     The four have codes in ISO 15924, like the scripts,
     but they are not values of the @('Script') property:")
   (xdoc::ul
    (xdoc::li
     "@('Hanb'), Han with Bopomofo:
      Chinese written with Han characters and Bopomofo.")
    (xdoc::li
     "@('Hntl'), traditional Han with Latin:
      Han characters and Latin letters.
      The specification has it from Unicode 18.0.0 on.")
    (xdoc::li
     "@('Jpan'), Japanese: Han characters, Hiragana and Katakana.")
    (xdoc::li
     "@('Kore'), Korean: Hangul and Han characters."))
   (xdoc::p
    "A text in Japanese mixes three scripts and is not a deception;
     with @('Jpan') in the augmented script set
     of each of its characters,
     its resolved script set is not empty."))
  (:script ((script script)))
  (:han-with-bopomofo ())
  (:traditional-han-with-latin ())
  (:japanese ())
  (:korean ())
  :pred writing-system-p)

;;;;;;;;;;;;;;;;;;;;

(define writing-system-code ((system writing-system-p))
  :returns (code stringp)
  :short "The four-letter code of a script
          or of a writing system that uses several scripts."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the code in ISO 15924:
     for a script, the one that @(tsee script-code) returns."))
  (writing-system-case system
                       :script (script-code system.script)
                       :han-with-bopomofo "Hanb"
                       :traditional-han-with-latin "Hntl"
                       :japanese "Jpan"
                       :korean "Kore")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist writing-system-list
  :short "Fixtype of lists of scripts
          and writing systems that use several scripts."
  :elt-type writing-system
  :true-listp t
  :elementp-of-nil nil
  :pred writing-system-listp)

;;;;;;;;;;;;;;;;;;;;

(define writing-system-list-codes ((systems writing-system-listp))
  :returns (codes string-listp
                  :hints (("Goal" :induct t :in-theory (enable string-listp))))
  :short "The four-letter codes of the elements of a list of scripts
          and writing systems that use several scripts."
  (cond ((endp systems) nil)
        (t (cons (writing-system-code (car systems))
                 (writing-system-list-codes (cdr systems)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define scripts-to-writing-systems ((scripts script-listp))
  :returns (systems writing-system-listp :hints (("Goal" :induct t)))
  :short "Turn a list of scripts
          into a list of elements of sets of scripts."
  (cond ((endp scripts) nil)
        (t (cons (writing-system-script (car scripts))
                 (scripts-to-writing-systems (cdr scripts)))))
  :hooks (:fix)

  ///

  (defrule consp-of-scripts-to-writing-systems
    (equal (consp (scripts-to-writing-systems scripts))
           (consp scripts))
    :induct t)

  (defrule scripts-to-writing-systems-under-iff
    (iff (scripts-to-writing-systems scripts)
         (consp scripts))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum script-set
  :short "Fixtype of the sets of scripts
          that mixed-script detection uses."
  :long
  (xdoc::topstring
   (xdoc::p
    "A set is either ALL, the set of all scripts,
     or a finite set, given by the list of its elements,
     which are scripts and writing systems that use several scripts
     (see @(tsee writing-system)).
     The list stands for a set:
     the functions here build lists without duplicates.")
   (xdoc::p
    "We keep ALL apart, as the specification does,
     and do not list its elements:
     which scripts there are depends on the version of Unicode,
     and all that matters about ALL
     is that its intersection with a set is that set."))
  (:all ())
  (:of ((members writing-system-list)))
  :pred script-set-p)

;;;;;;;;;;;;;;;;;;;;

(define script-set-empty-p ((set script-set-p))
  :returns (yes/no booleanp)
  :short "Check if a set of scripts is empty."
  (script-set-case set
                   :all nil
                   :of (endp set.members))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define script-set-in ((system writing-system-p) (set script-set-p))
  :returns (yes/no booleanp)
  :short "Check if a script, or a writing system that uses several scripts,
          is in a set of scripts."
  (script-set-case set
                   :all t
                   :of (and (member-equal (writing-system-fix system)
                                          set.members)
                            t))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define script-set-intersect ((set1 script-set-p) (set2 script-set-p))
  :returns (set script-set-p)
  :short "The intersection of two sets of scripts."
  :long
  (xdoc::topstring
   (xdoc::p
    "The intersection of ALL with a set is that set.
     The elements of the intersection of two finite sets
     are in the order of the first one."))
  (script-set-case
   set1
   :all (script-set-fix set2)
   :of (script-set-case
        set2
        :all (script-set-fix set1)
        :of (script-set-of (intersection-equal set1.members set2.members))))
  :hooks (:fix)

  ///

  (defrule script-set-intersect-when-all-left
    (implies (equal (script-set-kind set1) :all)
             (equal (script-set-intersect set1 set2)
                    (script-set-fix set2))))

  (defrule script-set-intersect-when-all-right
    (implies (equal (script-set-kind set2) :all)
             (equal (script-set-intersect set1 set2)
                    (script-set-fix set1))))

  (defrule script-set-in-of-script-set-intersect
    (equal (script-set-in system (script-set-intersect set1 set2))
           (and (script-set-in system set1)
                (script-set-in system set2)))
    :enable script-set-in)

  (defrule script-set-intersect-associative
    (equal (script-set-intersect (script-set-intersect set1 set2) set3)
           (script-set-intersect set1 (script-set-intersect set2 set3)))
    :prep-lemmas
    ((defrule lemma
       (equal (intersection-equal (intersection-equal x y) z)
              (intersection-equal x (intersection-equal y z)))
       :induct (len x)
       :enable (intersection-equal
                len))))

  (defrule script-set-empty-p-of-script-set-intersect-when-empty-left
    (implies (script-set-empty-p set1)
             (script-set-empty-p (script-set-intersect set1 set2)))
    :enable script-set-empty-p)

  (defrule script-set-empty-p-of-script-set-intersect-when-empty-right
    (implies (script-set-empty-p set2)
             (script-set-empty-p (script-set-intersect set1 set2)))
    :enable script-set-empty-p))

;;;;;;;;;;;;;;;;;;;;

(define script-sets-intersect-p ((set1 script-set-p) (set2 script-set-p))
  :returns (yes/no booleanp)
  :short "Check if two sets of scripts have an element in common."
  (not (script-set-empty-p (script-set-intersect set1 set2)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define augment-script-extensions ((scripts script-listp) (ver versionp))
  :returns (set script-set-p)
  :short "The augmented script set that goes with
          a value of the @('Script_Extensions') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the definition of [UTS #39, Section 5.1].
     A set that contains @('Zyyy') (@('Common'))
     or @('Zinh') (@('Inherited')) is treated as ALL.
     To any other set are added
     the writing systems that use several scripts:")
   (xdoc::ul
    (xdoc::li
     "If the set contains @('Hani') (@('Han')),
      add @('Hanb'), @('Jpan') and @('Kore'),
      and from Unicode 18.0.0 on, @('Hntl').")
    (xdoc::li
     "If the set contains @('Hira') (@('Hiragana')), add @('Jpan').")
    (xdoc::li
     "If the set contains @('Kana') (@('Katakana')), add @('Jpan').")
    (xdoc::li
     "If the set contains @('Hang') (@('Hangul')), add @('Kore').")
    (xdoc::li
     "If the set contains @('Bopo') (@('Bopomofo')), add @('Hanb').")
    (xdoc::li
     "From Unicode 18.0.0 on,
      if the set contains @('Latn') (@('Latin')), add @('Hntl')."))
   (xdoc::p
    "See @(tsee writing-system) for what these four are.
     In the result, the scripts come first, in the order of the argument,
     and then the added writing systems, in the order of their codes."))
  (b* ((scripts (script-list-fix scripts))
       ((when (or (member-equal (script-common) scripts)
                  (member-equal (script-inherited) scripts)))
        (script-set-all))
       (han (member-equal (script-han) scripts))
       (hanb (or han
                 (member-equal (script-bopomofo) scripts)))
       (hntl (and (version<= (version-v18.0.0) ver)
                  (or han
                      (member-equal (script-latin) scripts))))
       (jpan (or han
                 (member-equal (script-hiragana) scripts)
                 (member-equal (script-katakana) scripts)))
       (kore (or han
                 (member-equal (script-hangul) scripts))))
    (script-set-of
     (append (scripts-to-writing-systems scripts)
             (and hanb (list (writing-system-han-with-bopomofo)))
             (and hntl (list (writing-system-traditional-han-with-latin)))
             (and jpan (list (writing-system-japanese)))
             (and kore (list (writing-system-korean))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-augmented-script-set ((cp code-point-p) (ver versionp))
  :returns (set script-set-p)
  :short "The augmented script set of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the @('Script_Extensions') of the code point,
     treated as ALL if it contains @('Common') or @('Inherited'),
     and otherwise with the writing systems that use several scripts added:
     see @(tsee augment-script-extensions).
     It is never empty."))
  (augment-script-extensions (code-point-script-extensions cp ver) ver)
  :hooks (:fix)

  ///

  (defrule not-script-set-empty-p-of-code-point-augmented-script-set
    (not (script-set-empty-p (code-point-augmented-script-set cp ver)))
    :enable (augment-script-extensions
             script-set-empty-p)
    :disable consp-of-code-point-script-extensions
    :use consp-of-code-point-script-extensions))

;;;;;;;;;;;;;;;;;;;;

(define resolved-script-set ((cps code-point-listp) (ver versionp))
  :returns (set script-set-p)
  :short "The resolved script set of a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the intersection of the augmented script sets
     of the code points of the list [UTS #39, Section 5.1].
     For the empty list it is ALL."))
  (cond ((endp cps) (script-set-all))
        (t (script-set-intersect
            (code-point-augmented-script-set (car cps) ver)
            (resolved-script-set (cdr cps) ver))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule resolved-script-set-of-append
    (equal (resolved-script-set (append cps1 cps2) ver)
           (script-set-intersect (resolved-script-set cps1 ver)
                                 (resolved-script-set cps2 ver)))
    :induct (resolved-script-set cps1 ver)))

;;;;;;;;;;;;;;;;;;;;

(define single-script-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points is single-script,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that its resolved script set is not empty
     [UTS #39, Section 5.1]:
     there is a script, or a writing system that uses several scripts,
     in which all its code points can be used.
     There can be several.
     A list that is not single-script is mixed-script:
     see @(tsee mixed-script-p)."))
  (not (script-set-empty-p (resolved-script-set cps ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define mixed-script-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points is mixed-script,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that its resolved script set is empty
     [UTS #39, Section 5.1]."))
  (script-set-empty-p (resolved-script-set cps ver))
  :hooks (:fix)

  ///

  (defruled mixed-script-p-in-terms-of-single-script-p
    (equal (mixed-script-p cps ver)
           (not (single-script-p cps ver)))
    :enable single-script-p)

  (defrule mixed-script-p-of-append-when-mixed-script-p-left
    (implies (mixed-script-p cps1 ver)
             (mixed-script-p (append cps1 cps2) ver)))

  (defrule mixed-script-p-of-append-when-mixed-script-p-right
    (implies (mixed-script-p cps2 ver)
             (mixed-script-p (append cps1 cps2) ver))))
