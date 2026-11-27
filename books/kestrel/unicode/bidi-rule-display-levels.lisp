; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rule-display-weak")
(include-book "bidi-resolved-levels")
(include-book "bidi-display")

(local (include-book "bidi-guarded-plain"))
(local (include-book "bidi-guarded-brackets"))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable fix nfix)))

(local (in-theory (disable acl2::equal-of-append-repeat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book proves that the Unicode Bidirectional Algorithm [UAX #9]
; gives the levels of BIDI-NAME-LEVELS to a name that satisfies the wide rule
; and has a letter of class R or AL or a digit of class AN,
; in a paragraph from left to right.  A second theorem is for a paragraph
; from right to left, when the first character of the name is not a mark:
; the levels are then those of BIDI-MIDDLE-LEVELS for the whole name.
; The theorems are at the end; every other event is local.
;
; The plan of the proof.  A name of that kind is plain text
; (theorem BIDI-PARAGRAPH-ALL-LEVELS-WHEN-PLAIN): it is one sequence
; at level 0, and its levels come from the weak rules, rule N0 on the
; bracket pairs, rules N1 and N2, the implicit levels and rule L1.
;
; 1. The classes after the weak rules are known
;    (book bidi-rule-display-weak.lisp).  In the three parts of the name,
;    they are: only L and ON before the first letter; the classes of the
;    clusters of the middle part, none of them L, the first of them R;
;    and only ON after the middle part.
; 2. Rule N0 changes some classes ON to R and nothing else (REFINES).
;    It changes nothing before the first letter, because no bracket is
;    there, and nothing after the middle part: a pair is set only if a
;    class R, AN or EN is strictly inside it, and that is so exactly when
;    a letter or a digit is strictly inside it (PAIR-AGREES).  This holds
;    for each pair when its turn comes because no two pairs cross
;    (theorem BIDI-PAIRS-NESTED-P-OF-BIDI-BRACKET-PAIRS): the brackets
;    and marks that an earlier pair has set are not strictly inside a
;    later pair.  The class at the end of the middle part is R, AN or EN:
;    it is the class of a letter or a digit, of a mark after one, or of a
;    closing bracket that rule N0 has set, or of a mark after it.
; 3. Rules N1 and N2 then give L to the first and to the third part,
;    and R to every ON of the middle part; so the levels are 0, then 2
;    for AN and EN and 1 for the rest of the middle part, then 0
;    (LEVELS-OF-THREE-PARTS).  Rule L1 changes nothing.
; 4. The levels 1 and 2 of the middle part are those of
;    BIDI-MIDDLE-LEVELS (LEV-OF-BIDI-CLUSTERS-WEAK-CLASSES).
; 5. In a paragraph from right to left the name is one sequence at level 1
;    (theorem BIDI-PARAGRAPH-ALL-LEVELS-WHEN-PLAIN-AT-LEVEL).
;    The classes after the weak rules are the same as in step 1,
;    because the name does not start with a mark.  Rule N0 still changes
;    some classes ON to R and nothing else: no class L is inside a pair.
;    Rules N1 and N2 give R to every ON, so the levels are 2 for AN and EN
;    and 1 for the rest, as in step 4 for the whole name.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules N1 and N2 and the implicit levels, on a list of classes in three parts:
; first only L and ON, then a part without L that starts and ends
; with R, AN or EN, then only ON.

(local
 (define pre-p (x)
   :returns (yes/no booleanp)
   (or (atom x)
       (and (member-eq (bidi-class-kind (car x))
                       '(:left-to-right :other-neutral))
            (pre-p (cdr x))))
   :verify-guards nil
   :hooks nil))

(local
 (define mid-p (x)
   :returns (yes/no booleanp)
   (or (atom x)
       (and (member-eq (bidi-class-kind (car x))
                       '(:right-to-left
                         :arabic-number
                         :european-number
                         :other-neutral))
            (mid-p (cdr x))))
   :verify-guards nil
   :hooks nil))

(local
 (define neutrals-p (x)
   :returns (yes/no booleanp)
   (or (atom x)
       (and (equal (bidi-class-kind (car x)) :other-neutral)
            (neutrals-p (cdr x))))
   :verify-guards nil
   :hooks nil))

(local
 (define strong-r-p (class)
   :returns (yes/no booleanp)
   (and (member-eq (bidi-class-kind class)
                   '(:right-to-left :arabic-number :european-number))
        t)
   :verify-guards nil
   :hooks nil))

(local
 (define ends-with-r (x)
   :returns (yes/no booleanp)
   (and (consp x)
        (if (consp (cdr x))
            (ends-with-r (cdr x))
          (strong-r-p (car x))))
   :verify-guards nil
   :hooks nil))

(local
 (define to-r ((x bidi-class-listp))
   :returns (new-x bidi-class-listp)
   (if (endp x)
       nil
     (cons (if (equal (bidi-class-kind (car x)) :other-neutral)
               (bidi-class-right-to-left)
             (bidi-class-fix (car x)))
           (to-r (cdr x))))
   :hooks nil))

(local
 (define lev ((x bidi-class-listp))
   :returns (levels nat-listp)
   (if (endp x)
       nil
     (cons (if (member-eq (bidi-class-kind (car x))
                          '(:european-number :arabic-number))
               2
             1)
           (lev (cdr x))))
   :hooks nil))

(defrulel bidi-n1-n2-of-append-when-pre-p
  (implies (and (pre-p p)
                (equal previous (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-n1-n2 (append p x) previous eos embedding)
                  (append (acl2::repeat (len p) (bidi-class-left-to-right))
                          (bidi-n1-n2 x previous eos embedding))))
  :induct (len p)
  :enable (len
           append
           pre-p
           acl2::repeat
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((:free (a b p s e) (bidi-n1-n2 (cons a b) p s e))))

(defrulel bidi-neutral-run-end-when-neutrals-p
  (implies (neutrals-p x)
           (equal (bidi-neutral-run-end x eos)
                  (bidi-class-fix eos)))
  :induct (len x)
  :enable (len
           neutrals-p
           bidi-neutral-run-end
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p))

(defrulel bidi-n1-n2-when-neutrals-p
  (implies (and (neutrals-p x)
                (equal previous (bidi-class-right-to-left))
                (equal eos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-n1-n2 x previous eos embedding)
                  (acl2::repeat (len x) (bidi-class-left-to-right))))
  :induct (len x)
  :enable (len
           neutrals-p
           acl2::repeat
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p)
  :expand ((:free (p s e) (bidi-n1-n2 x p s e))))

(defrulel bidi-neutral-run-end-of-append-when-ends-with-r
  (implies (and (mid-p m)
                (ends-with-r m))
           (equal (bidi-neutral-run-end (append m x) eos)
                  (bidi-class-right-to-left)))
  :induct (len m)
  :enable (len
           append
           mid-p
           ends-with-r
           strong-r-p
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((:free (a b s) (bidi-neutral-run-end (cons a b) s))))

(defrulel bidi-n1-n2-of-append-when-ends-with-r
  (implies (and (mid-p m)
                (ends-with-r m)
                (neutrals-p x)
                (equal previous (bidi-class-right-to-left))
                (equal eos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-n1-n2 (append m x) previous eos embedding)
                  (append (to-r m)
                          (acl2::repeat (len x) (bidi-class-left-to-right)))))
  :induct (len m)
  :enable (len
           append
           mid-p
           ends-with-r
           strong-r-p
           to-r
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((:free (a b p s e) (bidi-n1-n2 (cons a b) p s e))
           (:free (a b s) (bidi-neutral-run-end (cons a b) s))))

(defrulel bidi-n1-n2-of-append-when-starts-and-ends-with-r
  (implies (and (mid-p m)
                (ends-with-r m)
                (strong-r-p (car m))
                (neutrals-p x)
                (equal eos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-n1-n2 (append m x) previous eos embedding)
                  (append (to-r m)
                          (acl2::repeat (len x) (bidi-class-left-to-right)))))
  :enable (mid-p
           ends-with-r
           strong-r-p
           to-r
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((:free (a b p s e) (bidi-n1-n2 (cons a b) p s e))
           (:free (a b s) (bidi-neutral-run-end (cons a b) s))
           (append m x)
           (to-r m)))

(defrulel bidi-implicit-levels-of-append
  (equal (bidi-implicit-levels (append x y) level)
         (append (bidi-implicit-levels x level)
                 (bidi-implicit-levels y level)))
  :induct (len x)
  :enable (len bidi-implicit-levels))

(defrulel bidi-implicit-levels-of-repeat-of-left-to-right
  (implies (and (equal class (bidi-class-left-to-right))
                (equal level 0))
           (equal (bidi-implicit-levels (acl2::repeat n class) level)
                  (acl2::repeat n 0)))
  :induct (acl2::repeat n class)
  :enable (acl2::repeat
           bidi-implicit-level)
  :expand ((:free (a b) (bidi-implicit-levels (cons a b) 0))
           (bidi-implicit-levels nil 0)))

(defrulel bidi-implicit-levels-of-to-r
  (implies (and (mid-p m)
                (equal level 0))
           (equal (bidi-implicit-levels (to-r m) level)
                  (lev m)))
  :induct (len m)
  :enable (len
           mid-p
           to-r
           lev
           bidi-implicit-level)
  :expand ((:free (a b) (bidi-implicit-levels (cons a b) 0))
           (bidi-implicit-levels nil 0)))

(defrulel levels-of-three-parts
  (implies (and (pre-p p)
                (mid-p m)
                (ends-with-r m)
                (strong-r-p (car m))
                (neutrals-p x)
                (equal sos (bidi-class-left-to-right))
                (equal eos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right))
                (equal level 0))
           (equal (bidi-implicit-levels
                   (bidi-n1-n2 (append p m x) sos eos embedding)
                   level)
                  (append (acl2::repeat (len p) 0)
                          (lev m)
                          (acl2::repeat (len x) 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The levels of the closed form of the classes after the weak rules
; are the levels of BIDI-MIDDLE-LEVELS.

(defrulel lev-of-append
  (equal (lev (append x y))
         (append (lev x)
                 (lev y)))
  :induct (len x)
  :enable (len lev append))

(defrulel lev-of-repeat
  (equal (lev (acl2::repeat n class))
         (acl2::repeat n
                       (if (member-eq (bidi-class-kind class)
                                      '(:european-number :arabic-number))
                           2
                         1)))
  :induct (acl2::repeat n class)
  :enable (acl2::repeat lev))

(defrulel repeat-of-+
  (implies (and (natp m)
                (natp n))
           (equal (acl2::repeat (+ m n) x)
                  (append (acl2::repeat m x)
                          (acl2::repeat n x))))
  :induct (acl2::repeat m x)
  :enable acl2::repeat)

(defrulel number-kind-of-bidi-cluster-weak-class
  (iff (member-eq (bidi-class-kind
                   (bidi-cluster-weak-class cluster previous next arabic ver))
                  '(:european-number :arabic-number))
       (or (bidi-cluster-digit-kind cluster arabic ver)
           (bidi-cluster-joins-p cluster previous next arabic ver)))
  :enable (bidi-cluster-weak-class
           bidi-cluster-digit-kind))

(defrulel not-bidi-cluster-joins-p-when-previous-is-not-digit
  (implies (not (bidi-cluster-digit-kind previous arabic ver))
           (not (bidi-cluster-joins-p cluster previous next arabic ver)))
  :enable bidi-cluster-joins-p)

(defrulel not-bidi-cluster-digit-kind-when-bidi-cluster-joins-p
  (implies (bidi-cluster-joins-p cluster previous next arabic ver)
           (not (bidi-cluster-digit-kind cluster arabic2 ver)))
  :enable (bidi-cluster-joins-p
           bidi-cluster-digit-kind))

(defrulel bidi-cluster-digit-kind-under-iff
  (implies (syntaxp (not (equal arabic ''nil)))
           (iff (bidi-cluster-digit-kind cluster arabic ver)
                (bidi-cluster-digit-kind cluster nil ver)))
  :enable bidi-cluster-digit-kind)

(defrulel bidi-arabic-after-cluster-p-when-digit
  (implies (and (bidi-cluster-digit-kind cluster nil ver)
                (booleanp arabic))
           (equal (bidi-arabic-after-cluster-p cluster arabic ver)
                  arabic))
  :enable (bidi-arabic-after-cluster-p
           bidi-cluster-digit-kind))

(defrulel bidi-arabic-after-cluster-p-when-joins
  (implies (and (bidi-cluster-joins-p cluster previous next arabic2 ver)
                (booleanp arabic))
           (equal (bidi-arabic-after-cluster-p cluster arabic ver)
                  arabic))
  :enable (bidi-arabic-after-cluster-p
           bidi-cluster-joins-p))

; BIDI-MIDDLE-LEVELS, one or two clusters at a time.

(defruledl bidi-middle-levels-when-not-digit
  (implies (and (consp clusters)
                (not (bidi-cluster-digit-kind (car clusters) nil ver)))
           (equal (bidi-middle-levels clusters arabic ver)
                  (append (acl2::repeat (len (car clusters)) 1)
                          (bidi-middle-levels
                           (cdr clusters)
                           (bidi-arabic-after-cluster-p (car clusters)
                                                        arabic
                                                        ver)
                           ver))))
  :expand ((bidi-middle-levels clusters arabic ver)
           (bidi-leading-number clusters arabic ver)
           (bidi-after-leading-number clusters arabic ver)))

(defruledl bidi-middle-levels-when-digit
  (implies (and (consp clusters)
                (bidi-cluster-digit-kind (car clusters) nil ver)
                (not (and (consp (cdr clusters))
                          (bidi-cluster-joins-p (cadr clusters)
                                                (car clusters)
                                                (caddr clusters)
                                                arabic
                                                ver))))
           (equal (bidi-middle-levels clusters arabic ver)
                  (append (acl2::repeat (len (car clusters)) 2)
                          (bidi-middle-levels (cdr clusters) arabic ver))))
  :expand ((bidi-middle-levels clusters arabic ver)
           (bidi-middle-levels (cdr clusters) arabic ver)
           (bidi-leading-number clusters arabic ver)
           (bidi-after-leading-number clusters arabic ver)
           (:free (a b) (acl2::flatten (cons a b)))))

(defruledl bidi-middle-levels-when-digit-and-joined
  (implies (and (consp clusters)
                (bidi-cluster-digit-kind (car clusters) nil ver)
                (consp (cdr clusters))
                (bidi-cluster-joins-p (cadr clusters)
                                      (car clusters)
                                      (caddr clusters)
                                      arabic
                                      ver))
           (equal (bidi-middle-levels clusters arabic ver)
                  (append (acl2::repeat (len (car clusters)) 2)
                          (acl2::repeat (len (cadr clusters)) 2)
                          (bidi-middle-levels (cddr clusters) arabic ver))))
  :expand ((bidi-middle-levels clusters arabic ver)
           (bidi-middle-levels (cddr clusters) arabic ver)
           (bidi-leading-number clusters arabic ver)
           (bidi-after-leading-number clusters arabic ver)
           (:free (a b) (acl2::flatten (cons a b)))))

(defrulel not-bidi-cluster-joins-p-of-car-when-not-consp
  (implies (not (consp clusters))
           (not (bidi-cluster-joins-p (car clusters) previous next arabic ver)))
  :enable (bidi-cluster-joins-p
           acl2::default-car))

(defrulel bidi-middle-levels-when-not-consp
  (implies (not (consp clusters))
           (equal (bidi-middle-levels clusters arabic ver)
                  nil))
  :expand ((bidi-middle-levels clusters arabic ver)
           (bidi-leading-number clusters arabic ver)
           (bidi-after-leading-number clusters arabic ver)))

(local
 (define bridge-induction (clusters previous arabic ver)
   (declare (ignorable previous))
   (cond ((atom clusters) nil)
         ((not (bidi-cluster-digit-kind (car clusters) nil ver))
          (bridge-induction (cdr clusters)
                            (car clusters)
                            (bidi-arabic-after-cluster-p (car clusters)
                                                         arabic
                                                         ver)
                            ver))
         ((and (consp (cdr clusters))
               (bidi-cluster-joins-p (cadr clusters)
                                     (car clusters)
                                     (caddr clusters)
                                     arabic
                                     ver))
          (bridge-induction (cddr clusters) (cadr clusters) arabic ver))
         (t (bridge-induction (cdr clusters) (car clusters) arabic ver)))
   :measure (len clusters)
   :hints (("Goal" :in-theory (enable len o-p o-finp o<)))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel lev-of-bidi-clusters-weak-classes
  (implies (and (not (bidi-cluster-joins-p (car clusters)
                                           previous
                                           (cadr clusters)
                                           arabic
                                           ver))
                (booleanp arabic))
           (equal (lev (bidi-clusters-weak-classes clusters
                                                   previous
                                                   arabic
                                                   ver))
                  (bidi-middle-levels clusters arabic ver)))
  :induct (bridge-induction clusters previous arabic ver)
  :enable (bridge-induction
           bidi-middle-levels-when-not-digit
           bidi-middle-levels-when-digit
           bidi-middle-levels-when-digit-and-joined)
  :expand ((bidi-clusters-weak-classes clusters previous arabic ver)
           (:free (p a) (bidi-clusters-weak-classes (cdr clusters) p a ver))
           (bidi-middle-levels nil arabic ver)
           (bidi-leading-number nil arabic ver)
           (bidi-after-leading-number nil arabic ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The closed form of the classes after the weak rules, on three lists of
; clusters: clusters without letters and digits, any clusters, and
; clusters without letters, digits and marks at their starts.

(defrulel take-of-+-of-append-of-repeat
  (implies (and (natp m)
                (natp n))
           (equal (take (+ m n) (append (acl2::repeat m x) y))
                  (append (acl2::repeat m x)
                          (take n y))))
  :induct (acl2::repeat m x)
  :enable (acl2::repeat take))

(defrulel nthcdr-of-+-of-append-of-repeat
  (implies (and (natp m)
                (natp n))
           (equal (nthcdr (+ m n) (append (acl2::repeat m x) y))
                  (nthcdr n y)))
  :induct (acl2::repeat m x)
  :enable (acl2::repeat nthcdr))

(defrulel take-of-append-of-repeat
  (implies (natp m)
           (equal (take m (append (acl2::repeat m x) y))
                  (acl2::repeat m x)))
  :use (:instance take-of-+-of-append-of-repeat (n 0))
  :disable take-of-+-of-append-of-repeat)

(defrulel nthcdr-of-append-of-repeat
  (implies (natp m)
           (equal (nthcdr m (append (acl2::repeat m x) y))
                  y))
  :use (:instance nthcdr-of-+-of-append-of-repeat (n 0))
  :disable nthcdr-of-+-of-append-of-repeat)

(defrulel pre-p-of-append
  (equal (pre-p (append x y))
         (and (pre-p x)
              (pre-p y)))
  :induct (len x)
  :enable (len pre-p append))

(defrulel pre-p-of-repeat
  (implies (member-eq (bidi-class-kind class)
                      '(:left-to-right :other-neutral))
           (pre-p (acl2::repeat n class)))
  :induct (acl2::repeat n class)
  :enable (acl2::repeat pre-p))

(defrulel neutrals-p-of-append
  (equal (neutrals-p (append x y))
         (and (neutrals-p x)
              (neutrals-p y)))
  :induct (len x)
  :enable (len neutrals-p append))

(defrulel neutrals-p-of-repeat
  (implies (equal (bidi-class-kind class) :other-neutral)
           (neutrals-p (acl2::repeat n class)))
  :induct (acl2::repeat n class)
  :enable (acl2::repeat neutrals-p))

(local
 (define plain-cluster-p (cluster ver)
   :returns (yes/no booleanp)
   (not (member-eq (bidi-class-kind (code-point-bidi-class (car cluster) ver))
                   '(:right-to-left
                     :arabic-letter
                     :european-number
                     :arabic-number
                     :left-to-right)))
   :verify-guards nil
   :hooks nil))

(local
 (define plain-clusters-p (clusters ver)
   :returns (yes/no booleanp)
   (or (atom clusters)
       (and (plain-cluster-p (car clusters) ver)
            (plain-clusters-p (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(local
 (define tail-clusters-p (clusters ver)
   :returns (yes/no booleanp)
   (or (atom clusters)
       (and (plain-cluster-p (car clusters) ver)
            (not (bidi-mark-code-point-p (car (car clusters)) ver))
            (tail-clusters-p (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel plain-cluster-p-of-code-point-list-fix
  (implies (consp cluster)
           (equal (plain-cluster-p (code-point-list-fix cluster) ver)
                  (plain-cluster-p cluster ver)))
  :enable plain-cluster-p)

(defrulel not-bidi-cluster-digit-kind-when-plain-cluster-p
  (implies (plain-cluster-p cluster ver)
           (not (bidi-cluster-digit-kind cluster arabic ver)))
  :enable (plain-cluster-p bidi-cluster-digit-kind))

(defrulel bidi-cluster-digit-kind-when-not-consp
  (implies (not (consp cluster))
           (equal (bidi-cluster-digit-kind cluster arabic ver)
                  nil))
  :enable bidi-cluster-digit-kind)

(defrulel not-bidi-cluster-joins-p-when-next-is-not-digit
  (implies (not (bidi-cluster-digit-kind next nil ver))
           (not (bidi-cluster-joins-p cluster previous next arabic ver)))
  :enable (bidi-cluster-joins-p
           bidi-cluster-digit-kind))

(defrulel bidi-cluster-weak-class-when-plain-cluster-p
  (implies (and (plain-cluster-p cluster ver)
                (not (bidi-cluster-digit-kind previous nil ver)))
           (member-eq (bidi-class-kind
                       (bidi-cluster-weak-class cluster
                                                previous
                                                next
                                                arabic
                                                ver))
                      '(:left-to-right :other-neutral)))
  :enable (plain-cluster-p
           bidi-cluster-weak-class))

(defrulel bidi-arabic-after-cluster-p-when-plain-cluster-p
  (implies (plain-cluster-p cluster ver)
           (equal (bidi-arabic-after-cluster-p cluster nil ver)
                  nil))
  :enable (plain-cluster-p
           bidi-arabic-after-cluster-p))

(defruledl bidi-clusters-weak-classes-when-previous-is-not-digit
  (implies (and (syntaxp (not (equal previous ''nil)))
                (not (bidi-cluster-digit-kind previous nil ver)))
           (equal (bidi-clusters-weak-classes clusters previous arabic ver)
                  (bidi-clusters-weak-classes clusters nil arabic ver)))
  :expand ((bidi-clusters-weak-classes clusters previous arabic ver)
           (bidi-clusters-weak-classes clusters nil arabic ver))
  :enable bidi-cluster-weak-class)

(local
 (define clusters-induction (clusters previous arabic ver)
   (declare (ignorable previous arabic))
   (if (atom clusters)
       nil
     (clusters-induction (cdr clusters)
                         (code-point-list-fix (car clusters))
                         (bidi-arabic-after-cluster-p (car clusters) arabic ver)
                         ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel pre-p-of-take-of-bidi-clusters-weak-classes
  (implies (and (plain-clusters-p clusters ver)
                (not (bidi-cluster-digit-kind previous nil ver)))
           (pre-p (take (len (acl2::flatten clusters))
                        (bidi-clusters-weak-classes (append clusters more)
                                                    previous
                                                    nil
                                                    ver))))
  :induct (clusters-induction clusters previous nil ver)
  :enable (clusters-induction
           plain-clusters-p
           append)
  :expand ((:free (a b p) (bidi-clusters-weak-classes (cons a b) p nil ver))
           (:free (a b) (acl2::flatten (cons a b)))
           (acl2::flatten clusters)))

(defrulel nthcdr-of-bidi-clusters-weak-classes-when-plain
  (implies (and (plain-clusters-p clusters ver)
                (not (bidi-cluster-digit-kind previous nil ver)))
           (equal (nthcdr (len (acl2::flatten clusters))
                          (bidi-clusters-weak-classes (append clusters more)
                                                      previous
                                                      nil
                                                      ver))
                  (bidi-clusters-weak-classes more nil nil ver)))
  :induct (clusters-induction clusters previous nil ver)
  :enable (clusters-induction
           plain-clusters-p
           append
           bidi-clusters-weak-classes-when-previous-is-not-digit)
  :expand ((:free (a b p) (bidi-clusters-weak-classes (cons a b) p nil ver))
           (:free (a b) (acl2::flatten (cons a b)))
           (acl2::flatten clusters)))

(defrulel take-of-bidi-clusters-weak-classes-of-append
  (implies (not (bidi-cluster-digit-kind (car more) nil ver))
           (equal (take (len (acl2::flatten clusters))
                        (bidi-clusters-weak-classes (append clusters more)
                                                    previous
                                                    arabic
                                                    ver))
                  (bidi-clusters-weak-classes clusters previous arabic ver)))
  :induct (clusters-induction clusters previous arabic ver)
  :enable (clusters-induction
           append
           bidi-cluster-weak-class)
  :expand ((:free (a b p) (bidi-clusters-weak-classes (cons a b) p arabic ver))
           (bidi-clusters-weak-classes clusters previous arabic ver)
           (bidi-clusters-weak-classes nil previous arabic ver)
           (:free (a b) (acl2::flatten (cons a b)))
           (acl2::flatten clusters)))

(defrulel neutrals-p-of-bidi-clusters-weak-classes-when-tail
  (implies (tail-clusters-p clusters ver)
           (neutrals-p
            (bidi-clusters-weak-classes clusters previous arabic ver)))
  :induct (clusters-induction clusters previous arabic ver)
  :enable (clusters-induction
           tail-clusters-p
           plain-cluster-p
           bidi-cluster-weak-class
           bidi-cluster-digit-kind
           bidi-mark-code-point-p)
  :expand ((bidi-clusters-weak-classes clusters previous arabic ver)
           (tail-clusters-p (cdr clusters) ver))
  :disable bidi-cluster-digit-kind-under-iff)

(defrulel neutrals-p-of-nthcdr-of-bidi-clusters-weak-classes
  (implies (tail-clusters-p more ver)
           (neutrals-p
            (nthcdr (len (acl2::flatten clusters))
                    (bidi-clusters-weak-classes (append clusters more)
                                                previous
                                                arabic
                                                ver))))
  :induct (clusters-induction clusters previous arabic ver)
  :enable (clusters-induction
           append)
  :expand ((:free (a b p) (bidi-clusters-weak-classes (cons a b) p arabic ver))
           (:free (a b) (acl2::flatten (cons a b)))
           (acl2::flatten clusters)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The clusters of lists of code points.

(defrulel flatten-of-bidi-clusters
  (equal (acl2::flatten (bidi-clusters cps ver))
         (code-point-list-fix cps))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           acl2::flatten
           code-point-list-fix)
  :expand (acl2::flatten (bidi-clusters (cdr cps) ver)))

(defrulel consp-of-bidi-clusters
  (equal (consp (bidi-clusters cps ver))
         (consp cps))
  :expand (bidi-clusters cps ver))

(defrulel bidi-clusters-when-not-consp
  (implies (not (consp cps))
           (equal (bidi-clusters cps ver)
                  nil))
  :expand (bidi-clusters cps ver))

(defrulel consp-of-car-of-bidi-clusters
  (implies (consp cps)
           (consp (car (bidi-clusters cps ver))))
  :expand (bidi-clusters cps ver))

(defrulel car-of-car-of-bidi-clusters
  (implies (consp cps)
           (equal (car (car (bidi-clusters cps ver)))
                  (code-point-fix (car cps))))
  :expand (bidi-clusters cps ver))

(defrulel bidi-clusters-of-append
  (implies (not (and (consp y)
                     (bidi-mark-code-point-p (car y) ver)))
           (equal (bidi-clusters (append x y) ver)
                  (append (bidi-clusters x ver)
                          (bidi-clusters y ver))))
  :induct (bidi-clusters x ver)
  :enable bidi-clusters
  :expand (:free (a b) (bidi-clusters (cons a b) ver)))

; Code points that are neither letters nor digits, and are not of class L.

(local
 (define plain-cp (cp ver)
   :returns (yes/no booleanp)
   (not (member-eq (bidi-class-kind (code-point-bidi-class cp ver))
                   '(:right-to-left
                     :arabic-letter
                     :european-number
                     :arabic-number
                     :left-to-right)))
   :verify-guards nil
   :hooks nil))

(local
 (define plain-cps (cps ver)
   :returns (yes/no booleanp)
   (or (atom cps)
       (and (plain-cp (car cps) ver)
            (plain-cps (cdr cps) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel plain-clusters-p-of-bidi-clusters
  (implies (plain-cps cps ver)
           (plain-clusters-p (bidi-clusters cps ver) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           plain-cps
           plain-cp
           plain-clusters-p
           plain-cluster-p))

(defrulel tail-clusters-p-of-cdr-of-bidi-clusters
  (implies (plain-cps cps ver)
           (tail-clusters-p (cdr (bidi-clusters cps ver)) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           plain-cps
           plain-cp
           tail-clusters-p
           plain-cluster-p))

(defrulel tail-clusters-p-of-bidi-clusters
  (implies (and (plain-cps cps ver)
                (not (and (consp cps)
                          (bidi-mark-code-point-p (car cps) ver))))
           (tail-clusters-p (bidi-clusters cps ver) ver))
  :cases ((consp cps))
  :expand (tail-clusters-p (bidi-clusters cps ver) ver)
  :enable (plain-cluster-p
           plain-cps
           plain-cp
           tail-clusters-p))

; Clusters whose first code points are not marks and not of class L.

(local
 (define mid-clusters-p (clusters ver)
   :returns (yes/no booleanp)
   (or (atom clusters)
       (and (consp (car clusters))
            (not (member-eq (bidi-class-kind
                             (code-point-bidi-class (car (car clusters)) ver))
                            '(:left-to-right :nonspacing-mark)))
            (mid-clusters-p (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel mid-clusters-p-of-cdr-of-bidi-clusters
  (implies (not (bidi-class-kind-present-p :left-to-right cps ver))
           (mid-clusters-p (cdr (bidi-clusters cps ver)) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-class-kind-present-p
           mid-clusters-p
           bidi-mark-code-point-p))

(defrulel mid-clusters-p-of-bidi-clusters
  (implies (and (not (bidi-class-kind-present-p :left-to-right cps ver))
                (not (and (consp cps)
                          (bidi-mark-code-point-p (car cps) ver))))
           (mid-clusters-p (bidi-clusters cps ver) ver))
  :cases ((consp cps))
  :expand ((mid-clusters-p (bidi-clusters cps ver) ver)
           (bidi-class-kind-present-p :left-to-right cps ver))
  :enable (mid-clusters-p
           bidi-mark-code-point-p))

(defrulel mid-p-of-append
  (equal (mid-p (append x y))
         (and (mid-p x)
              (mid-p y)))
  :induct (len x)
  :enable (len mid-p append))

(defrulel mid-p-of-repeat
  (implies (member-eq (bidi-class-kind class)
                      '(:right-to-left
                        :arabic-number
                        :european-number
                        :other-neutral))
           (mid-p (acl2::repeat n class)))
  :induct (acl2::repeat n class)
  :enable (acl2::repeat mid-p))

(defrulel mid-p-of-bidi-clusters-weak-classes
  (implies (mid-clusters-p clusters ver)
           (mid-p (bidi-clusters-weak-classes clusters previous arabic ver)))
  :induct (clusters-induction clusters previous arabic ver)
  :enable (clusters-induction
           mid-clusters-p
           bidi-cluster-weak-class)
  :expand (bidi-clusters-weak-classes clusters previous arabic ver))

(defrulel car-of-append-of-repeat
  (implies (posp n)
           (equal (car (append (acl2::repeat n x) y))
                  x))
  :expand (acl2::repeat n x))

(defrulel strong-r-p-of-car-of-bidi-clusters-weak-classes
  (implies (and (consp clusters)
                (consp (car clusters))
                (bidi-right-to-left-letter-p (car (car clusters)) ver))
           (strong-r-p
            (car (bidi-clusters-weak-classes clusters previous arabic ver))))
  :enable (strong-r-p
           bidi-cluster-weak-class
           bidi-cluster-digit-kind
           bidi-cluster-joins-p
           bidi-right-to-left-letter-p
           len)
  :expand (bidi-clusters-weak-classes clusters previous arabic ver)
  :disable bidi-cluster-digit-kind-under-iff)

(defrulel not-bidi-cluster-digit-kind-of-car-of-bidi-clusters-when-plain
  (implies (plain-cps cps ver)
           (not (bidi-cluster-digit-kind (car (bidi-clusters cps ver))
                                         arabic
                                         ver)))
  :cases ((consp cps))
  :enable (bidi-cluster-digit-kind
           plain-cps
           plain-cp)
  :disable bidi-cluster-digit-kind-under-iff)

; The classes after the weak rules, for a list of code points in three parts.

(defrulel weak-classes-of-three-parts
  (implies (and (plain-cps before ver)
                (consp middle)
                (bidi-right-to-left-letter-p (car middle) ver)
                (plain-cps after ver)
                (not (and (consp after)
                          (bidi-mark-code-point-p (car after) ver))))
           (b* ((w (bidi-clusters-weak-classes
                    (bidi-clusters (append before middle after) ver)
                    nil
                    nil
                    ver)))
             (and (pre-p (take (len before) w))
                  (equal (take (len middle) (nthcdr (len before) w))
                         (bidi-clusters-weak-classes
                          (bidi-clusters middle ver)
                          nil
                          nil
                          ver))
                  (neutrals-p (nthcdr (len middle)
                                      (nthcdr (len before) w))))))
  :enable (bidi-right-to-left-letter-p
           bidi-mark-code-point-p)
  :disable (pre-p-of-take-of-bidi-clusters-weak-classes
            nthcdr-of-bidi-clusters-weak-classes-when-plain
            take-of-bidi-clusters-weak-classes-of-append
            neutrals-p-of-nthcdr-of-bidi-clusters-weak-classes
            acl2::nthcdr-of-nthcdr)
  :use ((:instance pre-p-of-take-of-bidi-clusters-weak-classes
                   (clusters (bidi-clusters before ver))
                   (more (append (bidi-clusters middle ver)
                                 (bidi-clusters after ver)))
                   (previous nil))
        (:instance nthcdr-of-bidi-clusters-weak-classes-when-plain
                   (clusters (bidi-clusters before ver))
                   (more (append (bidi-clusters middle ver)
                                 (bidi-clusters after ver)))
                   (previous nil))
        (:instance take-of-bidi-clusters-weak-classes-of-append
                   (clusters (bidi-clusters middle ver))
                   (more (bidi-clusters after ver))
                   (previous nil)
                   (arabic nil))
        (:instance neutrals-p-of-nthcdr-of-bidi-clusters-weak-classes
                   (clusters (bidi-clusters middle ver))
                   (more (bidi-clusters after ver))
                   (previous nil)
                   (arabic nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The three parts of a name that the wide rule allows
; and that has a letter of class R or AL or a digit of class AN.

(local (in-theory (enable fix)))

(local
 (define split-induction (start end x)
   (if (zp start)
       (list end x)
     (split-induction (- start 1) (- end 1) (cdr x)))
   :verify-guards nil
   :hooks nil))

(defrulel append-of-take-and-nthcdr-of-take
  (implies (and (natp start)
                (natp end)
                (<= start end))
           (equal (append (take start x)
                          (append (nthcdr start (take end x)) y))
                  (append (take end x) y)))
  :induct (split-induction start end x)
  :enable (split-induction take nthcdr))

(defrulel append-of-take-and-nthcdr-when-true-listp
  (implies (and (true-listp x)
                (natp end)
                (<= end (len x)))
           (equal (append (take end x) (nthcdr end x))
                  x))
  :induct (nthcdr end x)
  :enable (take nthcdr len))

; Before the first letter.

(defrulel plain-cps-of-take-of-bidi-name-start
  (implies (and (bidi-rule-wide-start-p name ver)
                (not (bidi-class-kind-present-p :left-to-right name ver)))
           (plain-cps (take (bidi-name-start name ver) name) ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           bidi-rule-wide-start-p
           bidi-class-kind-present-p
           bidi-right-to-left-letter-p
           plain-cps
           plain-cp
           take))

; The first letter.

(defrulel bidi-name-start-below-len
  (implies (and (bidi-rule-wide-start-p name ver)
                (bidi-right-to-left-label-p name ver))
           (< (bidi-name-start name ver) (len name)))
  :rule-classes (:rewrite :linear)
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           bidi-rule-wide-start-p
           bidi-right-to-left-label-p
           bidi-right-to-left-letter-p
           len)
  :expand ((bidi-class-kind-present-p :right-to-left name ver)
           (bidi-class-kind-present-p :arabic-letter name ver)
           (bidi-class-kind-present-p :arabic-number name ver)))

(defrulel bidi-right-to-left-letter-p-of-nth-of-bidi-name-start
  (implies (< (bidi-name-start name ver) (len name))
           (bidi-right-to-left-letter-p (nth (bidi-name-start name ver) name)
                                        ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start nth len))

(defrulel bidi-name-start-below-bidi-name-to-last-letter-or-digit
  (implies (< (bidi-name-start name ver) (len name))
           (< (bidi-name-start name ver)
              (bidi-name-to-last-letter-or-digit name ver)))
  :rule-classes :linear
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           bidi-name-to-last-letter-or-digit
           len))

(defrulel bidi-name-to-last-letter-or-digit-below-bidi-name-end
  (<= (bidi-name-to-last-letter-or-digit name ver)
      (bidi-name-end name ver))
  :rule-classes :linear
  :enable (bidi-name-end max))

; After the last letter or digit.

(defrulel plain-cps-when-no-letter-or-digit
  (implies (and (equal (bidi-name-to-last-letter-or-digit name ver) 0)
                (not (bidi-class-kind-present-p :left-to-right name ver)))
           (plain-cps name ver))
  :induct (bidi-name-to-last-letter-or-digit name ver)
  :enable (bidi-name-to-last-letter-or-digit
           bidi-class-kind-present-p
           bidi-right-to-left-letter-p
           bidi-digit-p
           plain-cps
           plain-cp))

(defrulel not-bidi-class-kind-present-p-of-nthcdr
  (implies (not (bidi-class-kind-present-p kind cps ver))
           (not (bidi-class-kind-present-p kind (nthcdr n cps) ver)))
  :induct (nthcdr n cps)
  :enable (nthcdr bidi-class-kind-present-p))

(defrulel plain-cps-of-nthcdr-when-after-last
  (implies (and (<= (bidi-name-to-last-letter-or-digit name ver) (nfix n))
                (not (bidi-class-kind-present-p :left-to-right name ver)))
           (plain-cps (nthcdr n name) ver))
  :induct (nthcdr n name)
  :enable (nthcdr
           bidi-name-to-last-letter-or-digit
           bidi-class-kind-present-p
           nfix))

(defrulel not-bidi-mark-code-point-p-of-nth-of-bidi-leading-marks
  (implies (< (bidi-leading-marks x ver) (len x))
           (not (bidi-mark-code-point-p (nth (bidi-leading-marks x ver) x)
                                        ver)))
  :induct (bidi-leading-marks x ver)
  :enable (bidi-leading-marks nth len))

(defrulel not-bidi-mark-code-point-p-of-nth-after-marks
  (implies (and (natp a)
                (< (+ a (bidi-leading-marks (nthcdr a x) ver))
                   (len x)))
           (not (bidi-mark-code-point-p
                 (nth (+ a (bidi-leading-marks (nthcdr a x) ver)) x)
                 ver)))
  :induct (nthcdr a x)
  :enable (nthcdr nth len))

(defrulel not-bidi-mark-code-point-p-of-nth-of-bidi-name-end
  (implies (< (bidi-name-end name ver) (len name))
           (not (bidi-mark-code-point-p (nth (bidi-name-end name ver) name)
                                        ver)))
  :enable (bidi-name-end max))

(defrulel not-bidi-class-kind-present-p-of-take
  (implies (and (not (bidi-class-kind-present-p kind cps ver))
                (<= (nfix n) (len cps)))
           (not (bidi-class-kind-present-p kind (take n cps) ver)))
  :induct (take n cps)
  :enable (take bidi-class-kind-present-p len nfix))

(defrulel not-bidi-mark-code-point-p-when-bidi-right-to-left-letter-p
  (implies (bidi-right-to-left-letter-p cp ver)
           (not (bidi-mark-code-point-p cp ver)))
  :enable (bidi-right-to-left-letter-p bidi-mark-code-point-p))

; The classes after the weak rules, in the three parts.

(defrulel weak-classes-of-name
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (b* ((start (bidi-name-start name ver))
                (end (bidi-name-end name ver))
                (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                               nil
                                               nil
                                               ver)))
             (and (pre-p (take start w))
                  (equal (take (- end start) (nthcdr start w))
                         (bidi-clusters-weak-classes
                          (bidi-clusters (nthcdr start (take end name)) ver)
                          nil
                          nil
                          ver))
                  (neutrals-p (nthcdr end w)))))
  :enable bidi-rule-wide-p
  :disable (weak-classes-of-three-parts)
  :use (:instance weak-classes-of-three-parts
                  (before (take (bidi-name-start name ver) name))
                  (middle (nthcdr (bidi-name-start name ver)
                                  (take (bidi-name-end name ver) name)))
                  (after (nthcdr (bidi-name-end name ver) name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of classes that is another list of classes
; except that some classes ON have become R.  Rule N0 does this.

(local
 (define refines (x y)
   :returns (yes/no booleanp)
   (if (atom x)
       (atom y)
     (and (consp y)
          (or (equal (bidi-class-kind (car y))
                     (bidi-class-kind (car x)))
              (and (equal (bidi-class-kind (car x)) :other-neutral)
                   (equal (bidi-class-kind (car y)) :right-to-left)))
          (refines (cdr x) (cdr y))))
   :verify-guards nil
   :hooks nil))

(local
 (define two-lists-induction (x y)
   (if (or (atom x)
           (atom y))
       nil
     (two-lists-induction (cdr x) (cdr y)))
   :verify-guards nil
   :hooks nil))

(local
 (define two-lists-and-count-induction (x y n)
   (if (or (zp n)
           (atom x)
           (atom y))
       nil
     (two-lists-and-count-induction (cdr x) (cdr y) (- n 1)))
   :verify-guards nil
   :hooks nil))

(defrulel refines-of-same
  (refines x x)
  :induct (len x)
  :enable (len refines))

(defrulel len-when-refines
  (implies (refines x y)
           (equal (len y)
                  (len x)))
  :induct (two-lists-induction x y)
  :enable (two-lists-induction refines len))

(defrulel refines-of-nthcdr
  (implies (refines x y)
           (refines (nthcdr n x) (nthcdr n y)))
  :induct (two-lists-and-count-induction x y n)
  :enable (two-lists-and-count-induction refines nthcdr))

(defrulel refines-of-take
  (implies (and (refines x y)
                (<= (nfix n) (len x)))
           (refines (take n x) (take n y)))
  :induct (two-lists-and-count-induction x y n)
  :enable (two-lists-and-count-induction refines take len))

(defrulel mid-p-when-refines
  (implies (and (refines x y)
                (mid-p x))
           (mid-p y))
  :induct (two-lists-induction x y)
  :enable (two-lists-induction refines mid-p))

(defrulel lev-when-refines
  (implies (refines x y)
           (equal (lev y)
                  (lev x)))
  :induct (two-lists-induction x y)
  :enable (two-lists-induction refines lev))

(defrulel strong-r-p-of-car-when-refines
  (implies (and (refines x y)
                (strong-r-p (car x)))
           (strong-r-p (car y)))
  :enable (refines strong-r-p acl2::default-car))

(defrulel ends-with-r-of-take
  (implies (and (posp n)
                (<= n (len x))
                (strong-r-p (nth (- n 1) x)))
           (ends-with-r (take n x)))
  :induct (take n x)
  :enable (take ends-with-r nth len))

(defrulel ends-with-r-of-take-of-nthcdr
  (implies (and (natp start)
                (natp end)
                (< start end)
                (<= end (len x))
                (strong-r-p (nth (- end 1) x)))
           (ends-with-r (take (- end start) (nthcdr start x))))
  :induct (split-induction start end x)
  :enable (split-induction nthcdr nth len))

(defrulel len-of-bidi-clusters-weak-classes
  (equal (len (bidi-clusters-weak-classes clusters previous arabic ver))
         (len (acl2::flatten clusters)))
  :induct (clusters-induction clusters previous arabic ver)
  :enable clusters-induction
  :expand ((bidi-clusters-weak-classes clusters previous arabic ver)
           (acl2::flatten clusters)))

(defrulel append-of-three-parts
  (implies (and (true-listp x)
                (natp start)
                (natp end)
                (<= start end)
                (<= end (len x)))
           (equal (append (take start x)
                          (take (- end start) (nthcdr start x))
                          (nthcdr end x))
                  x))
  :induct (split-induction start end x)
  :enable (split-induction take nthcdr len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The levels of a name, given what rule N0 does.

(defruledl levels-of-name-given-n0
  (b* ((start (bidi-name-start name ver))
       (end (bidi-name-end name ver))
       (w (bidi-clusters-weak-classes (bidi-clusters name ver) nil nil ver)))
    (implies (and (code-point-listp name)
                  (bidi-rule-wide-p name ver)
                  (bidi-right-to-left-label-p name ver)
                  (true-listp n0)
                  (refines w n0)
                  (pre-p (take start n0))
                  (neutrals-p (nthcdr end n0))
                  (strong-r-p (nth (- end 1) n0))
                  (equal sos (bidi-class-left-to-right))
                  (equal eos (bidi-class-left-to-right))
                  (equal embedding (bidi-class-left-to-right))
                  (equal level 0))
             (equal (bidi-implicit-levels (bidi-n1-n2 n0 sos eos embedding)
                                          level)
                    (bidi-name-levels name ver))))
  :enable (bidi-name-levels
           bidi-rule-wide-p)
  :disable (levels-of-three-parts
            weak-classes-of-name
            refines-of-take
            refines-of-nthcdr
            strong-r-p-of-car-when-refines)
  :use ((:instance levels-of-three-parts
                   (p (take (bidi-name-start name ver) n0))
                   (m (take (- (bidi-name-end name ver)
                               (bidi-name-start name ver))
                            (nthcdr (bidi-name-start name ver) n0)))
                   (x (nthcdr (bidi-name-end name ver) n0)))
        weak-classes-of-name
        (:instance refines-of-take
                   (n (- (bidi-name-end name ver)
                         (bidi-name-start name ver)))
                   (x (nthcdr (bidi-name-start name ver)
                              (bidi-clusters-weak-classes
                               (bidi-clusters name ver)
                               nil
                               nil
                               ver)))
                   (y (nthcdr (bidi-name-start name ver) n0)))
        (:instance strong-r-p-of-car-when-refines
                   (x (bidi-clusters-weak-classes
                       (bidi-clusters (nthcdr (bidi-name-start name ver)
                                              (take (bidi-name-end name ver)
                                                    name))
                                      ver)
                       nil
                       nil
                       ver))
                   (y (take (- (bidi-name-end name ver)
                               (bidi-name-start name ver))
                            (nthcdr (bidi-name-start name ver) n0))))
        (:instance len-when-refines
                   (x (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (y n0))
        (:instance refines-of-nthcdr
                   (n (bidi-name-start name ver))
                   (x (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (y n0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; What rule N0 needs to know about the classes after the weak rules,
; code point by code point:
; a letter or a digit has the class R, AN or EN;
; a mark has the class of the code point before it;
; a bracket has the class ON;
; and a code point of class R, AN or EN is a letter or a digit,
; or comes after one with no bracket from there on (CARRY says so).

(local
 (define l-o-d (cp ver)
   :returns (yes/no booleanp)
   (or (bidi-right-to-left-letter-p cp ver)
       (bidi-digit-p cp ver))
   :verify-guards nil
   :hooks nil))

(local
 (define wrel (cps w previous carry ver)
   :returns (yes/no booleanp)
   (b* (((when (atom cps)) (atom w))
        ((unless (consp w)) nil)
        (cp (car cps))
        (class (car w))
        (new-carry (and (or (l-o-d cp ver)
                            (and carry
                                 (not (code-point-bidi-bracket cp ver))))
                        t)))
     (and (implies (l-o-d cp ver)
                   (strong-r-p class))
          (implies (bidi-mark-code-point-p cp ver)
                   (equal (bidi-class-kind class)
                          (bidi-class-kind previous)))
          (implies (code-point-bidi-bracket cp ver)
                   (equal (bidi-class-kind class) :other-neutral))
          (implies (strong-r-p class)
                   new-carry)
          (wrel (cdr cps) (cdr w) class new-carry ver)))
   :verify-guards nil
   :hooks nil))

(defrulel not-l-o-d-when-mark
  (implies (bidi-mark-code-point-p cp ver)
           (not (l-o-d cp ver)))
  :enable (l-o-d
           bidi-mark-code-point-p
           bidi-right-to-left-letter-p
           bidi-digit-p))

(defrulel not-code-point-bidi-bracket-when-mark
  (implies (bidi-mark-code-point-p cp ver)
           (not (code-point-bidi-bracket cp ver)))
  :enable bidi-mark-code-point-p
  :use code-point-bidi-class-when-code-point-bidi-bracket
  :disable code-point-bidi-class-when-code-point-bidi-bracket)

(defrulel not-l-o-d-when-bracket
  (implies (code-point-bidi-bracket cp ver)
           (not (l-o-d cp ver)))
  :enable (l-o-d
           bidi-right-to-left-letter-p
           bidi-digit-p))

(defrulel wrel-of-append-of-marks
  (implies (and (bidi-marks-p marks ver)
                (booleanp carry)
                (implies (strong-r-p class)
                         carry))
           (equal (wrel (append marks rest)
                        (append (acl2::repeat (len marks) class) wrest)
                        class
                        carry
                        ver)
                  (wrel rest wrest class carry ver)))
  :induct (len marks)
  :enable (len
           append
           acl2::repeat)
  :expand ((:free (a b c d p k) (wrel (cons a b) (cons c d) p k ver))))

(defrulel wrel-of-marks
  (implies (and (bidi-marks-p marks ver)
                (booleanp carry)
                (implies (strong-r-p class)
                         carry))
           (equal (wrel (true-list-fix marks)
                        (append (acl2::repeat (len marks) class) wrest)
                        class
                        carry
                        ver)
                  (wrel nil wrest class carry ver)))
  :use (:instance wrel-of-append-of-marks (rest nil))
  :disable wrel-of-append-of-marks)

(defrulel wrel-of-marks-alone
  (implies (and (bidi-marks-p marks ver)
                (booleanp carry)
                (implies (strong-r-p class)
                         carry))
           (wrel (true-list-fix marks)
                 (acl2::repeat (len marks) class)
                 class
                 carry
                 ver))
  :use (:instance wrel-of-append-of-marks (rest nil) (wrest nil))
  :disable (wrel-of-append-of-marks
            wrel-of-marks)
  :expand (wrel nil nil class carry ver))

(defrulel bidi-clusters-weak-classes-when-not-consp
  (implies (not (consp clusters))
           (equal (bidi-clusters-weak-classes clusters previous arabic ver)
                  nil))
  :expand (bidi-clusters-weak-classes clusters previous arabic ver))

; The four facts for the class of a cluster.

(defrulel bidi-cluster-weak-class-when-letter-or-digit
  (implies (and (consp cluster)
                (l-o-d (car cluster) ver))
           (strong-r-p (bidi-cluster-weak-class cluster
                                                previous
                                                next
                                                arabic
                                                ver)))
  :enable (strong-r-p
           l-o-d
           bidi-right-to-left-letter-p
           bidi-digit-p
           bidi-cluster-weak-class
           bidi-cluster-digit-kind
           bidi-cluster-joins-p)
  :disable bidi-cluster-digit-kind-under-iff)

(defrulel bidi-cluster-weak-class-when-mark
  (implies (and (consp cluster)
                (bidi-mark-code-point-p (car cluster) ver))
           (equal (bidi-class-kind
                   (bidi-cluster-weak-class cluster previous next arabic ver))
                  :left-to-right))
  :enable (bidi-mark-code-point-p
           bidi-cluster-weak-class
           bidi-cluster-digit-kind
           bidi-cluster-joins-p)
  :disable bidi-cluster-digit-kind-under-iff)

(defrulel bidi-cluster-weak-class-when-bracket
  (implies (and (consp cluster)
                (code-point-bidi-bracket (car cluster) ver))
           (equal (bidi-class-kind
                   (bidi-cluster-weak-class cluster previous next arabic ver))
                  :other-neutral))
  :enable (bidi-cluster-weak-class
           bidi-cluster-digit-kind
           bidi-cluster-joins-p)
  :disable bidi-cluster-digit-kind-under-iff)

(defrulel not-strong-r-p-of-bidi-cluster-weak-class-when-bracket
  (implies (and (consp cluster)
                (code-point-bidi-bracket (car cluster) ver))
           (not (strong-r-p (bidi-cluster-weak-class cluster
                                                     previous
                                                     next
                                                     arabic
                                                     ver))))
  :enable strong-r-p)

(defrulel bidi-cluster-weak-class-when-strong
  (implies (and (consp cluster)
                (strong-r-p (bidi-cluster-weak-class cluster
                                                     previous
                                                     next
                                                     arabic
                                                     ver))
                (not (l-o-d (car cluster) ver)))
           (and (bidi-cluster-digit-kind previous nil ver)
                (not (code-point-bidi-bracket (car cluster) ver))))
  :enable (strong-r-p
           l-o-d
           bidi-right-to-left-letter-p
           bidi-digit-p
           bidi-cluster-weak-class
           bidi-cluster-digit-kind
           bidi-cluster-joins-p)
  :disable (bidi-cluster-digit-kind-under-iff
            code-point-bidi-class-when-code-point-bidi-bracket)
  :use (:instance code-point-bidi-class-when-code-point-bidi-bracket
                  (cp (car cluster))))

(defrulel bidi-cluster-digit-kind-when-not-letter-or-digit
  (implies (and (consp cluster)
                (not (l-o-d (car cluster) ver)))
           (not (bidi-cluster-digit-kind cluster arabic ver)))
  :enable (l-o-d
           bidi-digit-p
           bidi-cluster-digit-kind)
  :disable bidi-cluster-digit-kind-under-iff)

; The shape of clusters.

(local
 (define shape-ok (clusters ver)
   :returns (yes/no booleanp)
   (or (atom clusters)
       (and (consp (car clusters))
            (bidi-marks-p (cdr (car clusters)) ver)
            (shape-ok (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(local
 (define heads-proper (clusters ver)
   :returns (yes/no booleanp)
   (or (atom clusters)
       (and (not (bidi-mark-code-point-p (car (car clusters)) ver))
            (heads-proper (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel shape-of-bidi-clusters
  (and (shape-ok (bidi-clusters cps ver) ver)
       (heads-proper (cdr (bidi-clusters cps ver)) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           shape-ok
           heads-proper))

(local
 (define wrel-induction (clusters previous arabic pk carry ver)
   (declare (ignorable previous arabic pk carry))
   (if (atom clusters)
       nil
     (wrel-induction
      (cdr clusters)
      (code-point-list-fix (car clusters))
      (bidi-arabic-after-cluster-p (car clusters) arabic ver)
      (bidi-cluster-weak-class (car clusters)
                               previous
                               (cadr clusters)
                               arabic
                               ver)
      (and (or (l-o-d (car (car clusters)) ver)
               (and carry
                    (not (code-point-bidi-bracket (car (car clusters)) ver))))
           t)
      ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel repeat-of-1+
  (implies (natp n)
           (equal (acl2::repeat (+ 1 n) x)
                  (cons x (acl2::repeat n x))))
  :expand (acl2::repeat (+ 1 n) x)
  :disable repeat-of-+)

(defrulel wrel-of-flatten-and-bidi-clusters-weak-classes
  (implies (and (code-point-list-listp clusters)
                (shape-ok clusters ver)
                (heads-proper (cdr clusters) ver)
                (or (not (consp clusters))
                    (not (bidi-mark-code-point-p (car (car clusters)) ver))
                    (equal (bidi-class-kind pk) :left-to-right))
                (booleanp carry)
                (implies (bidi-cluster-digit-kind previous nil ver)
                         carry))
           (wrel (acl2::flatten clusters)
                 (bidi-clusters-weak-classes clusters previous arabic ver)
                 pk
                 carry
                 ver))
  :induct (wrel-induction clusters previous arabic pk carry ver)
  :enable (wrel-induction
           shape-ok
           heads-proper
           len)
  :expand ((bidi-clusters-weak-classes clusters previous arabic ver)
           (acl2::flatten clusters)
           (:free (a b c d p k) (wrel (cons a b) (cons c d) p k ver))
           (:free (p k) (wrel nil nil p k ver)))
  :disable (repeat-of-+
            bidi-cluster-digit-kind-under-iff)
  :prep-lemmas
  ((defrule lemma
     (implies (consp x)
              (equal (append x y)
                     (cons (car x) (append (cdr x) y))))
     :rule-classes ((:rewrite :backchain-limit-lst 0))
     :enable append)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The classes of a list of code points.

(local
 (define classes-of (cps ver)
   :returns (classes bidi-class-listp)
   (if (atom cps)
       nil
     (cons (code-point-bidi-class (car cps) ver)
           (classes-of (cdr cps) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-char-list-classes-of-code-points-to-bidi-chars
  (equal (bidi-char-list-classes (code-points-to-bidi-chars cps ver))
         (classes-of cps ver))
  :induct (len cps)
  :enable (len
           classes-of
           bidi-char-list-classes
           code-points-to-bidi-chars
           code-point-bidi-char))

(defrulel bidi-starts-with-mark-p-of-classes-of
  (equal (bidi-starts-with-mark-p (classes-of cps ver))
         (and (consp cps)
              (bidi-mark-code-point-p (car cps) ver)))
  :enable (bidi-starts-with-mark-p
           bidi-mark-code-point-p)
  :expand (classes-of cps ver))

(defrulel cdr-of-classes-of
  (equal (cdr (classes-of cps ver))
         (classes-of (cdr cps) ver))
  :expand ((classes-of cps ver)
           (classes-of (cdr cps) ver)))

(defrulel len-of-classes-of
  (equal (len (classes-of cps ver))
         (len cps))
  :induct (len cps)
  :enable (len classes-of))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists of classes without L.

(local
 (define no-l (x)
   :returns (yes/no booleanp)
   (or (atom x)
       (and (not (equal (bidi-class-kind (car x)) :left-to-right))
            (no-l (cdr x))))
   :verify-guards nil
   :hooks nil))

(defrulel no-l-when-refines
  (implies (and (refines x y)
                (no-l x))
           (no-l y))
  :induct (two-lists-induction x y)
  :enable (two-lists-induction refines no-l))

(defrulel no-l-when-mid-p
  (implies (mid-p x)
           (no-l x))
  :induct (len x)
  :enable (len mid-p no-l))

(defrulel no-l-when-neutrals-p
  (implies (neutrals-p x)
           (no-l x))
  :induct (len x)
  :enable (len neutrals-p no-l))

(defrulel no-l-of-append
  (equal (no-l (append x y))
         (and (no-l x)
              (no-l y)))
  :induct (len x)
  :enable (len no-l append))

; No class L is strictly inside a pair that opens in a part without L.

(defrulel not-bidi-n0-strong-inside-p-when-no-l
  (implies (and (no-l classes)
                (equal direction (bidi-class-left-to-right)))
           (not (bidi-n0-strong-inside-p classes position pair direction)))
  :induct (bidi-n0-strong-inside-p classes position pair direction)
  :enable (bidi-n0-strong-inside-p
           no-l
           bidi-class-direction))

(local
 (define list-and-two-counts-induction (x position k)
   (if (or (atom x)
           (zp k))
       position
     (list-and-two-counts-induction (cdr x) (+ 1 position) (- k 1)))
   :verify-guards nil
   :hooks nil))

(defrulel not-bidi-n0-strong-inside-p-when-no-l-from
  (implies (and (no-l (nthcdr k classes))
                (natp k)
                (natp position)
                (<= (+ position k) (+ 1 (bracket-pair->open pair)))
                (equal direction (bidi-class-left-to-right)))
           (not (bidi-n0-strong-inside-p classes position pair direction)))
  :induct (list-and-two-counts-induction classes position k)
  :enable (list-and-two-counts-induction
           nthcdr)
  :expand ((:free (d) (bidi-n0-strong-inside-p classes position pair d))))

; The direction before a pair that opens in a part without L,
; after a class R, AN or EN.

(defrulel bidi-n0-context-when-no-l
  (implies (and (no-l classes)
                (equal direction (bidi-class-right-to-left)))
           (equal (bidi-n0-context classes count direction)
                  (bidi-class-right-to-left)))
  :induct (bidi-n0-context classes count direction)
  :enable (bidi-n0-context
           no-l
           bidi-class-direction))

(local
 (define context-induction (classes count direction s)
   (if (or (atom classes)
           (zp s))
       (list count direction)
     (context-induction (cdr classes)
                        (- count 1)
                        (or (bidi-class-direction (car classes))
                            direction)
                        (- s 1)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n0-context-when-strong-r-before
  (implies (and (natp s)
                (natp count)
                (< s count)
                (< s (len classes))
                (strong-r-p (nth s classes))
                (no-l (nthcdr s classes)))
           (equal (bidi-n0-context classes count direction)
                  (bidi-class-right-to-left)))
  :induct (context-induction classes count direction s)
  :enable (context-induction
           nthcdr
           nth
           len
           no-l
           strong-r-p
           bidi-class-direction)
  :expand ((:free (d) (bidi-n0-context classes count d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A letter or a digit strictly inside a pair,
; and a class R, AN or EN strictly inside it.

(local
 (define inside-induction (cps w cur position pk carry ver)
   (declare (ignorable pk carry))
   (if (or (atom cps)
           (atom w)
           (atom cur))
       position
     (inside-induction
      (cdr cps)
      (cdr w)
      (cdr cur)
      (+ 1 position)
      (car w)
      (and (or (l-o-d (car cps) ver)
               (and carry
                    (not (code-point-bidi-bracket (car cps) ver))))
           t)
      ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n0-strong-inside-p-when-bidi-name-strong-inside-p
  (implies (and (wrel cps w pk carry ver)
                (refines w cur)
                (natp position)
                (bidi-name-strong-inside-p cps position pair ver)
                (equal direction (bidi-class-right-to-left)))
           (bidi-n0-strong-inside-p cur position pair direction))
  :induct (inside-induction cps w cur position pk carry ver)
  :enable (inside-induction
           wrel
           refines
           l-o-d
           strong-r-p
           bidi-class-direction)
  :expand ((bidi-name-strong-inside-p cps position pair ver)
           (:free (d) (bidi-n0-strong-inside-p cur position pair d))))

(defrulel bidi-name-strong-inside-p-when-bidi-n0-strong-inside-p
  (implies (and (wrel cps w pk carry ver)
                (natp position)
                (bidi-n0-strong-inside-p w position pair direction)
                (equal direction (bidi-class-right-to-left))
                (if (<= position (bracket-pair->open pair))
                    (code-point-bidi-bracket
                     (nth (- (bracket-pair->open pair) position) cps)
                     ver)
                  (not carry)))
           (bidi-name-strong-inside-p cps position pair ver))
  :induct (inside-induction cps w w position pk carry ver)
  :enable (inside-induction
           wrel
           l-o-d
           strong-r-p
           bidi-class-direction
           nth)
  :expand ((bidi-name-strong-inside-p cps position pair ver)
           (:free (d) (bidi-n0-strong-inside-p w position pair d)))
  :disable not-l-o-d-when-bracket
  :hints ('(:use (:instance not-l-o-d-when-bracket (cp (car cps))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Setting the two brackets of a pair, and the marks after them, to R.

(defrulel refines-transitive
  (implies (and (refines x y)
                (refines y z))
           (refines x z))
  :induct (three-lists-induction x y z)
  :enable (three-lists-induction refines)
  :prep-lemmas
  ((define three-lists-induction (x y z)
     (if (or (atom x)
             (atom y)
             (atom z))
         nil
       (three-lists-induction (cdr x) (cdr y) (cdr z)))
     :verify-guards nil
     :hooks nil)))

(local
 (define set-pair-induction (cps w cur position pair pk carry after ver)
   (declare (ignorable pk carry))
   (if (or (atom cps)
           (atom w)
           (atom cur))
       (list position pair after)
     (set-pair-induction
      (cdr cps)
      (cdr w)
      (cdr cur)
      (+ 1 position)
      pair
      (car w)
      (and (or (l-o-d (car cps) ver)
               (and carry
                    (not (code-point-bidi-bracket (car cps) ver))))
           t)
      (or (equal position (bracket-pair->open pair))
          (equal position (bracket-pair->close pair))
          (and after
               (bidi-mark-code-point-p (car cps) ver)))
      ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

; The result is the list with some ON changed to R.

(defrulel refines-of-bidi-n0-set-pair
  (implies (and (wrel cps w pk carry ver)
                (refines w cur)
                (natp position)
                (implies after
                         (equal (bidi-class-kind pk) :other-neutral))
                (implies (<= position (bracket-pair->open pair))
                         (code-point-bidi-bracket
                          (nth (- (bracket-pair->open pair) position) cps)
                          ver))
                (implies (<= position (bracket-pair->close pair))
                         (code-point-bidi-bracket
                          (nth (- (bracket-pair->close pair) position) cps)
                          ver))
                (equal direction (bidi-class-right-to-left)))
           (refines cur
                    (bidi-n0-set-pair cur
                                      (classes-of cps ver)
                                      position
                                      pair
                                      direction
                                      after)))
  :induct (set-pair-induction cps w cur position pair pk carry after ver)
  :enable (set-pair-induction
           wrel
           refines
           nth)
  :expand ((:free (o p d a) (bidi-n0-set-pair cur o p pair d a))))

(defrulel bidi-n0-set-pair-when-not-consp
  (implies (not (consp cur))
           (equal (bidi-n0-set-pair cur originals position pair direction after)
                  nil))
  :expand (bidi-n0-set-pair cur originals position pair direction after))

; Nothing changes before the opening bracket.

(local
 (define take-induction (cur originals position k)
   (if (or (zp k)
           (atom cur))
       (list originals position)
     (take-induction (cdr cur) (cdr originals) (+ 1 position) (- k 1)))
   :verify-guards nil
   :hooks nil))

(defrulel take-of-bidi-n0-set-pair
  (implies (and (bidi-class-listp cur)
                (natp k)
                (natp position)
                (<= (+ position k) (bracket-pair->open pair))
                (< (bracket-pair->open pair) (bracket-pair->close pair))
                (<= k (len cur))
                (not after))
           (equal (take k (bidi-n0-set-pair cur
                                            originals
                                            position
                                            pair
                                            direction
                                            after))
                  (take k cur)))
  :induct (take-induction cur originals position k)
  :enable (take-induction take len)
  :expand ((:free (p a) (bidi-n0-set-pair cur originals p pair direction a))))

; Nothing changes from a position after the closing bracket
; where no mark is.

(defrulel bidi-n0-set-pair-when-past
  (implies (and (bidi-class-listp cur)
                (natp position)
                (< (bracket-pair->open pair) position)
                (< (bracket-pair->close pair) position)
                (not after))
           (equal (bidi-n0-set-pair cur originals position pair direction after)
                  cur))
  :induct (bidi-n0-set-pair cur originals position pair direction after)
  :enable bidi-n0-set-pair)

(local
 (define nthcdr-induction (cur originals position k after pair)
   (if (or (zp k)
           (atom cur))
       (list originals position after)
     (nthcdr-induction
      (cdr cur)
      (cdr originals)
      (+ 1 position)
      (- k 1)
      (or (equal position (bracket-pair->open pair))
          (equal position (bracket-pair->close pair))
          (and after
               (bidi-starts-with-mark-p originals)))
      pair))
   :verify-guards nil
   :hooks nil))

(defrulel nthcdr-of-bidi-n0-set-pair
  (implies (and (bidi-class-listp cur)
                (natp k)
                (natp position)
                (< (bracket-pair->open pair) (+ position k))
                (< (bracket-pair->close pair) (+ position k))
                (not (bidi-starts-with-mark-p (nthcdr k originals))))
           (equal (nthcdr k (bidi-n0-set-pair cur
                                              originals
                                              position
                                              pair
                                              direction
                                              after))
                  (nthcdr k cur)))
  :induct (nthcdr-induction cur originals position k after pair)
  :enable (nthcdr-induction
           nthcdr
           bidi-class-list-fix
           bidi-starts-with-mark-p
           acl2::default-cdr
           acl2::default-car)
  :expand ((:free (p a) (bidi-n0-set-pair cur originals p pair direction a))))

; The closing bracket and the marks after it get the class R.

(local
 (define marks-induction (cur cps position k)
   (if (or (zp k)
           (atom cur))
       (list cps position)
     (marks-induction (cdr cur) (cdr cps) (+ 1 position) (- k 1)))
   :verify-guards nil
   :hooks nil))

(defrulel kind-of-nth-of-bidi-n0-set-pair-in-marks
  (implies (and after
                (natp k)
                (natp position)
                (< k (len cur))
                (< k (bidi-leading-marks cps ver)))
           (equal (bidi-class-kind
                   (nth k (bidi-n0-set-pair cur
                                            (classes-of cps ver)
                                            position
                                            pair
                                            direction
                                            after)))
                  (bidi-class-kind direction)))
  :induct (marks-induction cur cps position k)
  :enable (marks-induction
           nth
           len
           bidi-leading-marks)
  :expand ((:free (p a) (bidi-n0-set-pair cur
                                          (classes-of cps ver)
                                          p
                                          pair
                                          direction
                                          a))))

(local
 (define close-induction (cur cps position after pair ver)
   (if (or (atom cur)
           (not (natp position))
           (<= (bracket-pair->close pair) position))
       (list cps after)
     (close-induction
      (cdr cur)
      (cdr cps)
      (+ 1 position)
      (or (equal position (bracket-pair->open pair))
          (equal position (bracket-pair->close pair))
          (and after
               (consp cps)
               (bidi-mark-code-point-p (car cps) ver)))
      pair
      ver))
   :measure (nfix (- (bracket-pair->close pair) (nfix position)))
   :hints (("Goal" :in-theory (enable nfix o-p o-finp o<)))
   :verify-guards nil
   :hooks nil))

(defrulel kind-of-nth-of-bidi-n0-set-pair-after-close
  (implies (and (natp position)
                (<= position (bracket-pair->close pair))
                (natp k)
                (<= k (bidi-leading-marks
                       (nthcdr (+ 1 (- (bracket-pair->close pair) position))
                               cps)
                       ver))
                (< (+ (- (bracket-pair->close pair) position) k) (len cur)))
           (equal (bidi-class-kind
                   (nth (+ (- (bracket-pair->close pair) position) k)
                        (bidi-n0-set-pair cur
                                          (classes-of cps ver)
                                          position
                                          pair
                                          direction
                                          after)))
                  (bidi-class-kind direction)))
  :induct (close-induction cur cps position after pair ver)
  :enable (close-induction
           nth
           nthcdr
           len)
  :expand ((:free (p a) (bidi-n0-set-pair cur
                                          (classes-of cps ver)
                                          p
                                          pair
                                          direction
                                          a))
           (:free (a b) (nth k (cons a b)))))

; What is strictly inside a later pair does not change.

(local
 (define frame-induction (cur cps position x after ver)
   (if (atom cur)
       (list cps position after)
     (frame-induction
      (cdr cur)
      (cdr cps)
      (+ 1 position)
      x
      (or (equal position (bracket-pair->open x))
          (equal position (bracket-pair->close x))
          (and after
               (consp cps)
               (bidi-mark-code-point-p (car cps) ver)))
      ver))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n0-strong-inside-p-of-bidi-n0-set-pair
  (implies (and (bidi-pair-before-p x y)
                (< (bracket-pair->open y) (bracket-pair->close y))
                (natp position)
                (implies (<= position (bracket-pair->open y))
                         (not (bidi-mark-code-point-p
                               (nth (- (bracket-pair->open y) position) cps)
                               ver)))
                (implies after
                         (or (<= position (bracket-pair->open y))
                             (< (bracket-pair->close y) position))))
           (equal (bidi-n0-strong-inside-p
                   (bidi-n0-set-pair cur
                                     (classes-of cps ver)
                                     position
                                     x
                                     direction
                                     after)
                   position
                   y
                   d)
                  (bidi-n0-strong-inside-p cur position y d)))
  :induct (frame-induction cur cps position x after ver)
  :enable (frame-induction
           bidi-pair-before-p
           nth)
  :expand ((:free (p a) (bidi-n0-set-pair cur
                                          (classes-of cps ver)
                                          p
                                          x
                                          direction
                                          a))
           (:free (p) (bidi-n0-strong-inside-p cur p y d))
           (:free (a b p) (bidi-n0-strong-inside-p (cons a b) p y d))
           (:free (p) (bidi-n0-strong-inside-p nil p y d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The class after the last letter or digit and the marks after it.

(local
 (define wrel-list-induction (cps w pk carry ver)
   (declare (ignorable pk carry))
   (if (or (atom cps)
           (atom w))
       nil
     (wrel-list-induction
      (cdr cps)
      (cdr w)
      (car w)
      (and (or (l-o-d (car cps) ver)
               (and carry
                    (not (code-point-bidi-bracket (car cps) ver))))
           t)
      ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(local
 (define wrel-count-induction (cps w pk carry j ver)
   (declare (ignorable pk carry))
   (if (or (atom cps)
           (atom w)
           (zp j))
       nil
     (wrel-count-induction
      (cdr cps)
      (cdr w)
      (car w)
      (and (or (l-o-d (car cps) ver)
               (and carry
                    (not (code-point-bidi-bracket (car cps) ver))))
           t)
      (- j 1)
      ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel kind-of-nth-in-leading-marks-when-wrel
  (implies (and (wrel cps w pk carry ver)
                (natp j)
                (< j (bidi-leading-marks cps ver)))
           (equal (bidi-class-kind (nth j w))
                  (bidi-class-kind pk)))
  :induct (wrel-count-induction cps w pk carry j ver)
  :enable (wrel-count-induction
           wrel
           nth
           bidi-leading-marks)
  :expand ((wrel cps w pk carry ver)
           (bidi-leading-marks cps ver)))

(defrulel strong-r-p-of-nth-after-last-letter-or-digit
  (implies (and (wrel cps w pk carry ver)
                (< 0 (bidi-name-to-last-letter-or-digit cps ver))
                (natp k)
                (<= k (bidi-leading-marks
                       (nthcdr (bidi-name-to-last-letter-or-digit cps ver)
                               cps)
                       ver)))
           (strong-r-p
            (nth (+ -1 (bidi-name-to-last-letter-or-digit cps ver) k) w)))
  :induct (wrel-list-induction cps w pk carry ver)
  :enable (wrel-list-induction
           wrel
           l-o-d
           nth
           nthcdr
           bidi-name-to-last-letter-or-digit)
  :disable kind-of-nth-in-leading-marks-when-wrel
  :hints ('(:use (:instance kind-of-nth-in-leading-marks-when-wrel
                            (cps (cdr cps))
                            (w (cdr w))
                            (pk (car w))
                            (carry t)
                            (j (- k 1)))
                 :in-theory (enable strong-r-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More about lists with some ON changed to R.

(local
 (define two-lists-and-index-induction (x y i)
   (if (or (zp i)
           (atom x)
           (atom y))
       nil
     (two-lists-and-index-induction (cdr x) (cdr y) (- i 1)))
   :verify-guards nil
   :hooks nil))

(defrulel strong-r-p-of-nth-when-refines
  (implies (and (refines x y)
                (strong-r-p (nth i x)))
           (strong-r-p (nth i y)))
  :induct (two-lists-and-index-induction x y i)
  :enable (two-lists-and-index-induction
           refines
           strong-r-p
           nth
           acl2::default-car))

(defrulel kind-of-nth-when-refines-and-right-to-left
  (implies (and (refines x y)
                (equal (bidi-class-kind (nth i x)) :right-to-left))
           (equal (bidi-class-kind (nth i y))
                  :right-to-left))
  :induct (two-lists-and-index-induction x y i)
  :enable (two-lists-and-index-induction
           refines
           nth
           acl2::default-car))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0 on one pair.
; W-OK: from the position S on, the classes after the weak rules have no L,
; and the class at S is R, AN or EN.
; PAIR-FIT: the pair opens after S, at a bracket, and closes at a bracket.
; PAIR-AGREES: a class R, AN or EN is strictly inside the pair
; exactly when a letter or a digit is.

(local
 (define w-ok (w s)
   :returns (yes/no booleanp)
   (and (natp s)
        (< s (len w))
        (strong-r-p (nth s w))
        (no-l (nthcdr s w)))
   :verify-guards nil
   :hooks nil))

(local
 (define pair-fit (x cps s ver)
   :returns (yes/no booleanp)
   (and (< (nfix s) (bracket-pair->open x))
        (< (bracket-pair->open x) (bracket-pair->close x))
        (code-point-bidi-bracket (nth (bracket-pair->open x) cps) ver)
        (code-point-bidi-bracket (nth (bracket-pair->close x) cps) ver)
        t)
   :verify-guards nil
   :hooks nil))

(local
 (define pair-agrees (x cur cps ver)
   :returns (yes/no booleanp)
   (iff (bidi-n0-strong-inside-p cur 0 x (bidi-class-right-to-left))
        (bidi-name-strong-inside-p cps 0 x ver))
   :verify-guards nil
   :hooks nil))

(defrulel w-ok-forward
  (implies (w-ok w s)
           (and (natp s)
                (< s (len w))))
  :rule-classes :forward-chaining
  :enable w-ok)

(defrulel pair-fit-forward
  (implies (pair-fit x cps s ver)
           (and (< (nfix s) (bracket-pair->open x))
                (< (bracket-pair->open x) (bracket-pair->close x))))
  :rule-classes :forward-chaining
  :enable pair-fit)

(defruledl bidi-n0-pair-normal-form
  (implies (and (w-ok w s)
                (refines w cur)
                (pair-fit x cps s ver)
                (pair-agrees x cur cps ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-n0-pair cur (classes-of cps ver) x sos embedding)
                  (if (bidi-name-strong-inside-p cps 0 x ver)
                      (bidi-n0-set-pair cur
                                        (classes-of cps ver)
                                        0
                                        x
                                        (bidi-class-right-to-left)
                                        nil)
                    (bidi-class-list-fix cur))))
  :enable (bidi-n0-pair
           w-ok
           pair-fit
           pair-agrees)
  :disable (not-bidi-n0-strong-inside-p-when-no-l-from
            bidi-n0-context-when-strong-r-before
            refines-of-nthcdr
            no-l-when-refines
            strong-r-p-of-nth-when-refines)
  :use ((:instance not-bidi-n0-strong-inside-p-when-no-l-from
                   (classes cur)
                   (k s)
                   (position 0)
                   (pair x)
                   (direction (bidi-class-left-to-right)))
        (:instance bidi-n0-context-when-strong-r-before
                   (classes cur)
                   (count (bracket-pair->open x))
                   (direction (bidi-class-left-to-right)))
        (:instance refines-of-nthcdr (x w) (y cur) (n s))
        (:instance no-l-when-refines
                   (x (nthcdr s w))
                   (y (nthcdr s cur)))
        (:instance strong-r-p-of-nth-when-refines (x w) (y cur) (i s))
        (:instance len-when-refines (x w) (y cur))))

(defrulel not-bidi-mark-code-point-p-when-bracket
  (implies (code-point-bidi-bracket cp ver)
           (not (bidi-mark-code-point-p cp ver))))

(defrulel refines-of-bidi-class-list-fix
  (refines cur (bidi-class-list-fix cur))
  :induct (len cur)
  :enable (len refines bidi-class-list-fix))

(defrulel refines-of-bidi-class-list-fix-when-refines
  (implies (refines w cur)
           (refines w (bidi-class-list-fix cur)))
  :induct (two-lists-induction w cur)
  :enable (two-lists-induction refines bidi-class-list-fix))

(defrulel refines-of-bidi-n0-pair
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (pair-fit x cps s ver)
                (pair-agrees x cur cps ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (and (refines cur
                         (bidi-n0-pair cur
                                       (classes-of cps ver)
                                       x
                                       sos
                                       embedding))
                (refines w
                         (bidi-n0-pair cur
                                       (classes-of cps ver)
                                       x
                                       sos
                                       embedding))))
  :enable (bidi-n0-pair-normal-form
           pair-fit)
  :disable (refines-of-bidi-n0-set-pair
            refines-transitive)
  :use ((:instance refines-of-bidi-n0-set-pair
                   (position 0)
                   (pair x)
                   (direction (bidi-class-right-to-left))
                   (after nil))
        (:instance refines-transitive
                   (x w)
                   (y cur)
                   (z (bidi-n0-set-pair cur
                                        (classes-of cps ver)
                                        0
                                        x
                                        (bidi-class-right-to-left)
                                        nil)))))

; The later pairs.

(local
 (define pairs-fit (pairs cps s ver)
   :returns (yes/no booleanp)
   (or (atom pairs)
       (and (pair-fit (car pairs) cps s ver)
            (pairs-fit (cdr pairs) cps s ver)))
   :verify-guards nil
   :hooks nil))

(local
 (define pairs-agree (pairs cur cps ver)
   :returns (yes/no booleanp)
   (or (atom pairs)
       (and (pair-agrees (car pairs) cur cps ver)
            (pairs-agree (cdr pairs) cur cps ver)))
   :verify-guards nil
   :hooks nil))

(defrulel pairs-agree-of-bidi-class-list-fix
  (equal (pairs-agree pairs (bidi-class-list-fix cur) cps ver)
         (pairs-agree pairs cur cps ver))
  :induct (len pairs)
  :enable (len pairs-agree pair-agrees))

(defrulel pairs-agree-of-bidi-n0-set-pair
  (implies (and (pairs-agree pairs cur cps ver)
                (bidi-pair-before-all-p x pairs)
                (pairs-fit pairs cps s ver))
           (pairs-agree pairs
                        (bidi-n0-set-pair cur
                                          (classes-of cps ver)
                                          0
                                          x
                                          direction
                                          nil)
                        cps
                        ver))
  :induct (len pairs)
  :enable (len
           pairs-agree
           pair-agrees
           pairs-fit
           pair-fit
           bidi-pair-before-all-p))

(defrulel pairs-agree-of-bidi-n0-pair
  (implies (and (w-ok w s)
                (refines w cur)
                (pair-fit x cps s ver)
                (pair-agrees x cur cps ver)
                (pairs-agree pairs cur cps ver)
                (bidi-pair-before-all-p x pairs)
                (pairs-fit pairs cps s ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (pairs-agree pairs
                        (bidi-n0-pair cur (classes-of cps ver) x sos embedding)
                        cps
                        ver))
  :enable bidi-n0-pair-normal-form)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0 on all the pairs.

(defrulel refines-of-bidi-n0-pairs
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (pairs-fit pairs cps s ver)
                (bidi-pairs-nested-p pairs)
                (pairs-agree pairs cur cps ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (and (refines cur
                         (bidi-n0-pairs cur
                                        (classes-of cps ver)
                                        pairs
                                        sos
                                        embedding))
                (refines w
                         (bidi-n0-pairs cur
                                        (classes-of cps ver)
                                        pairs
                                        sos
                                        embedding))))
  :induct (bidi-n0-pairs cur (classes-of cps ver) pairs sos embedding)
  :enable (bidi-n0-pairs
           pairs-fit
           pairs-agree
           bidi-pairs-nested-p)
  :disable refines-transitive
  :hints ('(:use ((:instance refines-transitive
                             (x cur)
                             (y (bidi-n0-pair cur
                                              (classes-of cps ver)
                                              (car pairs)
                                              sos
                                              embedding))
                             (z (bidi-n0-pairs
                                 (bidi-n0-pair cur
                                               (classes-of cps ver)
                                               (car pairs)
                                               sos
                                               embedding)
                                 (classes-of cps ver)
                                 (cdr pairs)
                                 sos
                                 embedding)))))))

; Nothing changes up to the position S.

(defrulel take-of-bidi-n0-pairs
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (bidi-class-listp cur)
                (pairs-fit pairs cps s ver)
                (bidi-pairs-nested-p pairs)
                (pairs-agree pairs cur cps ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (take s (bidi-n0-pairs cur
                                         (classes-of cps ver)
                                         pairs
                                         sos
                                         embedding))
                  (take s cur)))
  :induct (bidi-n0-pairs cur (classes-of cps ver) pairs sos embedding)
  :enable (bidi-n0-pairs
           pairs-fit
           pairs-agree
           bidi-pairs-nested-p)
  :prep-lemmas
  ((defrule lemma
     (implies (and (w-ok w s)
                   (refines w cur)
                   (bidi-class-listp cur)
                   (pair-fit x cps s ver)
                   (pair-agrees x cur cps ver)
                   (equal sos (bidi-class-left-to-right))
                   (equal embedding (bidi-class-left-to-right)))
              (equal (take s (bidi-n0-pair cur
                                           (classes-of cps ver)
                                           x
                                           sos
                                           embedding))
                     (take s cur)))
     :enable (bidi-n0-pair-normal-form
              nfix)
     :disable take-of-bidi-n0-set-pair
     :use ((:instance take-of-bidi-n0-set-pair
                      (k s)
                      (originals (classes-of cps ver))
                      (position 0)
                      (pair x)
                      (direction (bidi-class-right-to-left))
                      (after nil))
           (:instance len-when-refines (x w) (y cur))
           w-ok-forward
           pair-fit-forward))))

; Nothing changes from a position on that is after the brackets
; of the pairs with letters or digits inside and where no mark is.

(defrulel nthcdr-of-classes-of
  (equal (nthcdr n (classes-of cps ver))
         (classes-of (nthcdr n cps) ver))
  :induct (nthcdr n cps)
  :enable (nthcdr classes-of))

(defrulel nthcdr-of-bidi-n0-pairs
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (bidi-class-listp cur)
                (pairs-fit pairs cps s ver)
                (bidi-pairs-nested-p pairs)
                (pairs-agree pairs cur cps ver)
                (natp e)
                (<= (bidi-name-pairs-end pairs cps ver) e)
                (not (and (consp (nthcdr e cps))
                          (bidi-mark-code-point-p (car (nthcdr e cps)) ver)))
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (nthcdr e (bidi-n0-pairs cur
                                           (classes-of cps ver)
                                           pairs
                                           sos
                                           embedding))
                  (nthcdr e cur)))
  :induct (bidi-n0-pairs cur (classes-of cps ver) pairs sos embedding)
  :enable (bidi-n0-pairs
           pairs-fit
           pairs-agree
           bidi-pairs-nested-p
           bidi-name-pairs-end
           max)
  :prep-lemmas
  ((defrule lemma-when-closed-before
     (implies (and (w-ok w s)
                   (refines w cur)
                   (bidi-class-listp cur)
                   (pair-fit x cps s ver)
                   (pair-agrees x cur cps ver)
                   (natp e)
                   (< (bracket-pair->close x) e)
                   (not (and (consp (nthcdr e cps))
                             (bidi-mark-code-point-p (car (nthcdr e cps))
                                                     ver)))
                   (equal sos (bidi-class-left-to-right))
                   (equal embedding (bidi-class-left-to-right)))
              (equal (nthcdr e (bidi-n0-pair cur
                                             (classes-of cps ver)
                                             x
                                             sos
                                             embedding))
                     (nthcdr e cur)))
     :enable bidi-n0-pair-normal-form
     :disable nthcdr-of-bidi-n0-set-pair
     :use ((:instance nthcdr-of-bidi-n0-set-pair
                      (k e)
                      (originals (classes-of cps ver))
                      (position 0)
                      (pair x)
                      (direction (bidi-class-right-to-left))
                      (after nil))
           pair-fit-forward))
   (defrule lemma-when-not-strong
     (implies (and (w-ok w s)
                   (refines w cur)
                   (bidi-class-listp cur)
                   (pair-fit x cps s ver)
                   (pair-agrees x cur cps ver)
                   (not (bidi-name-strong-inside-p cps 0 x ver))
                   (equal sos (bidi-class-left-to-right))
                   (equal embedding (bidi-class-left-to-right)))
              (equal (bidi-n0-pair cur (classes-of cps ver) x sos embedding)
                     cur))
     :enable bidi-n0-pair-normal-form)))

; The closing bracket of the last pair with a letter or a digit inside,
; and the marks after it, get the class R.

(defrulel kind-of-nth-of-bidi-n0-pairs
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (bidi-class-listp cur)
                (pairs-fit pairs cps s ver)
                (bidi-pairs-nested-p pairs)
                (pairs-agree pairs cur cps ver)
                (< 0 (bidi-name-pairs-end pairs cps ver))
                (natp k)
                (<= k (bidi-leading-marks
                       (nthcdr (bidi-name-pairs-end pairs cps ver) cps)
                       ver))
                (< (+ -1 (bidi-name-pairs-end pairs cps ver) k) (len cur))
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-class-kind
                   (nth (+ -1 (bidi-name-pairs-end pairs cps ver) k)
                        (bidi-n0-pairs cur
                                       (classes-of cps ver)
                                       pairs
                                       sos
                                       embedding)))
                  :right-to-left))
  :induct (bidi-n0-pairs cur (classes-of cps ver) pairs sos embedding)
  :enable (bidi-n0-pairs
           pairs-fit
           pairs-agree
           bidi-pairs-nested-p
           bidi-name-pairs-end
           max)
  :disable (kind-of-nth-when-refines-and-right-to-left
            refines-of-bidi-n0-pairs)
  :hints ('(:use ((:instance kind-of-nth-when-refines-and-right-to-left
                             (x (bidi-n0-pair cur
                                              (classes-of cps ver)
                                              (car pairs)
                                              sos
                                              embedding))
                             (y (bidi-n0-pairs
                                 (bidi-n0-pair cur
                                               (classes-of cps ver)
                                               (car pairs)
                                               sos
                                               embedding)
                                 (classes-of cps ver)
                                 (cdr pairs)
                                 sos
                                 embedding))
                             (i (+ k (bracket-pair->close (car pairs)))))
                  (:instance refines-of-bidi-n0-pairs
                             (cur (bidi-n0-pair cur
                                                (classes-of cps ver)
                                                (car pairs)
                                                sos
                                                embedding))
                             (pairs (cdr pairs))))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (w-ok w s)
                   (refines w cur)
                   (bidi-class-listp cur)
                   (pair-fit x cps s ver)
                   (pair-agrees x cur cps ver)
                   (bidi-name-strong-inside-p cps 0 x ver)
                   (natp k)
                   (<= k (bidi-leading-marks
                          (nthcdr (+ 1 (bracket-pair->close x)) cps)
                          ver))
                   (< (+ (bracket-pair->close x) k) (len cur))
                   (equal sos (bidi-class-left-to-right))
                   (equal embedding (bidi-class-left-to-right)))
              (equal (bidi-class-kind
                      (nth (+ k (bracket-pair->close x))
                           (bidi-n0-pair cur
                                         (classes-of cps ver)
                                         x
                                         sos
                                         embedding)))
                     :right-to-left))
     :enable bidi-n0-pair-normal-form
     :disable kind-of-nth-of-bidi-n0-set-pair-after-close
     :use (:instance kind-of-nth-of-bidi-n0-set-pair-after-close
                     (position 0)
                     (pair x)
                     (direction (bidi-class-right-to-left))
                     (after nil)))
   (defrule len-of-bidi-n0-pair-here
     (equal (len (bidi-n0-pair cur originals x sos embedding))
            (len cur)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The pairs of a name.

(local
 (define roles-of (cps ver)
   :returns (roles bidi-bracket-role-listp)
   (bidi-char-list-brackets (code-points-to-bidi-chars cps ver))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-bracket-role-kind-of-nth-of-roles-of
  (equal (bidi-bracket-role-kind (nth i (roles-of name ver)))
         (if (< (nfix i) (len name))
             (bidi-bracket-role-kind
              (code-point-bidi-bracket-role (nth i name) ver))
           :none))
  :induct (nth i name)
  :enable (roles-of
           nth
           len
           bidi-char-list-brackets
           code-points-to-bidi-chars
           code-point-bidi-char
           nfix))

(defrulel code-point-bidi-bracket-when-role
  (implies (not (equal (bidi-bracket-role-kind
                        (code-point-bidi-bracket-role cp ver))
                       :none))
           (code-point-bidi-bracket cp ver))
  :enable code-point-bidi-bracket-role)

(defrulel bidi-roles-neutral-p-of-roles-of
  (bidi-roles-neutral-p (roles-of cps ver) (classes-of cps ver))
  :induct (len cps)
  :enable (len
           roles-of
           classes-of
           bidi-roles-neutral-p
           bidi-char-list-brackets
           code-points-to-bidi-chars
           code-point-bidi-char))

; No bracket is before the first letter or at it.

(defrulel bidi-name-start-below-bracket
  (implies (and (bidi-rule-wide-start-p name ver)
                (natp i)
                (< i (len name))
                (code-point-bidi-bracket (nth i name) ver))
           (< (bidi-name-start name ver) i))
  :rule-classes (:rewrite :linear)
  :induct (nth i name)
  :enable (nth
           len
           bidi-name-start
           bidi-rule-wide-start-p
           bidi-right-to-left-letter-p)
  :disable code-point-bidi-class-when-code-point-bidi-bracket
  :hints ('(:use (:instance code-point-bidi-class-when-code-point-bidi-bracket
                            (cp (car name))))))

(defrulel pairs-fit-when-bidi-pairs-sound-p
  (implies (and (bidi-pairs-sound-p pairs
                                    (classes-of name ver)
                                    (roles-of name ver))
                (bidi-rule-wide-start-p name ver))
           (pairs-fit pairs name (bidi-name-start name ver) ver))
  :induct (len pairs)
  :enable (len
           bidi-pairs-sound-p
           bidi-pair-sound-p
           pairs-fit
           pair-fit
           nfix))

(defrulel pairs-agree-at-the-start
  (implies (and (wrel cps w pk carry ver)
                (pairs-fit pairs cps s ver))
           (pairs-agree pairs w cps ver))
  :induct (len pairs)
  :enable (len
           pairs-fit
           pair-fit
           pairs-agree
           pair-agrees)
  :disable (bidi-n0-strong-inside-p-when-bidi-name-strong-inside-p
            bidi-name-strong-inside-p-when-bidi-n0-strong-inside-p)
  :hints ('(:use ((:instance
                   bidi-n0-strong-inside-p-when-bidi-name-strong-inside-p
                   (cur w)
                   (position 0)
                   (pair (car pairs))
                   (direction (bidi-class-right-to-left)))
                  (:instance
                   bidi-name-strong-inside-p-when-bidi-n0-strong-inside-p
                   (position 0)
                   (pair (car pairs))
                   (direction (bidi-class-right-to-left)))))))

; The classes after the weak rules, for the lemmas above.

(defrulel no-l-when-two-parts
  (implies (and (mid-p (take k y))
                (neutrals-p (nthcdr k y))
                (<= (nfix k) (len y)))
           (no-l y))
  :induct (take k y)
  :enable (take nthcdr mid-p no-l len nfix))

(defrulel wrel-of-name
  (implies (and (code-point-listp name)
                (equal pk (bidi-class-left-to-right)))
           (wrel name
                 (bidi-clusters-weak-classes (bidi-clusters name ver)
                                             nil
                                             nil
                                             ver)
                 pk
                 nil
                 ver))
  :disable wrel-of-flatten-and-bidi-clusters-weak-classes
  :use (:instance wrel-of-flatten-and-bidi-clusters-weak-classes
                  (clusters (bidi-clusters name ver))
                  (previous nil)
                  (arabic nil)
                  (pk (bidi-class-left-to-right))
                  (carry nil)))

(defrulel strong-r-p-of-nth-when-wrel
  (implies (and (wrel cps w pk carry ver)
                (natp i)
                (< i (len cps))
                (l-o-d (nth i cps) ver))
           (strong-r-p (nth i w)))
  :induct (wrel-count-induction cps w pk carry i ver)
  :enable (wrel-count-induction
           nth
           len)
  :expand (:free (p k) (wrel cps w p k ver)))

(defrulel mid-p-of-weak-classes-of-middle
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (mid-p (bidi-clusters-weak-classes
                   (bidi-clusters (nthcdr (bidi-name-start name ver)
                                          (take (bidi-name-end name ver) name))
                                  ver)
                   nil
                   nil
                   ver)))
  :enable bidi-rule-wide-p
  :use (bidi-name-start-below-len
        bidi-name-start-below-bidi-name-to-last-letter-or-digit
        bidi-name-to-last-letter-or-digit-below-bidi-name-end
        bidi-right-to-left-letter-p-of-nth-of-bidi-name-start))

(defrulel no-l-of-nthcdr-of-weak-classes
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (no-l (nthcdr (bidi-name-start name ver)
                         (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                     nil
                                                     nil
                                                     ver))))
  :enable bidi-rule-wide-p
  :disable (weak-classes-of-name
            no-l-when-two-parts)
  :use (weak-classes-of-name
        (:instance no-l-when-two-parts
                   (k (- (bidi-name-end name ver)
                         (bidi-name-start name ver)))
                   (y (nthcdr (bidi-name-start name ver)
                              (bidi-clusters-weak-classes
                               (bidi-clusters name ver)
                               nil
                               nil
                               ver))))))

(defrulel w-ok-of-name
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (w-ok (bidi-clusters-weak-classes (bidi-clusters name ver)
                                             nil
                                             nil
                                             ver)
                 (bidi-name-start name ver)))
  :enable (w-ok
           bidi-rule-wide-p
           l-o-d)
  :disable (strong-r-p-of-nth-when-wrel
            bidi-right-to-left-letter-p-of-nth-of-bidi-name-start)
  :use ((:instance strong-r-p-of-nth-when-wrel
                   (cps name)
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (i (bidi-name-start name ver)))
        bidi-right-to-left-letter-p-of-nth-of-bidi-name-start))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0 on a name.

(defrulel bidi-char-list-brackets-of-code-points-to-bidi-chars
  (equal (bidi-char-list-brackets (code-points-to-bidi-chars cps ver))
         (roles-of cps ver))
  :enable roles-of)

(defrulel pairs-of-name
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (b* ((pairs (bidi-bracket-pairs (classes-of name ver)
                                           (roles-of name ver)))
                (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                               nil
                                               nil
                                               ver)))
             (and (pairs-fit pairs name (bidi-name-start name ver) ver)
                  (pairs-agree pairs w name ver))))
  :enable bidi-rule-wide-p
  :disable pairs-agree-at-the-start
  :use (:instance pairs-agree-at-the-start
                  (cps name)
                  (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                 nil
                                                 nil
                                                 ver))
                  (pk (bidi-class-left-to-right))
                  (carry nil)
                  (pairs (bidi-bracket-pairs (classes-of name ver)
                                             (roles-of name ver)))
                  (s (bidi-name-start name ver))))

(defrulel n0-of-name
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (b* ((w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                               nil
                                               nil
                                               ver))
                (n0 (bidi-n0-pairs w
                                   (classes-of name ver)
                                   (bidi-bracket-pairs (classes-of name ver)
                                                       (roles-of name ver))
                                   sos
                                   embedding)))
             (and (refines w n0)
                  (equal (take (bidi-name-start name ver) n0)
                         (take (bidi-name-start name ver) w))
                  (equal (nthcdr (bidi-name-end name ver) n0)
                         (nthcdr (bidi-name-end name ver) w)))))
  :disable (refines-of-bidi-n0-pairs
            take-of-bidi-n0-pairs
            nthcdr-of-bidi-n0-pairs
            pairs-of-name
            w-ok-of-name
            wrel-of-name)
  :enable (bidi-name-end max)
  :use (pairs-of-name
        w-ok-of-name
        (:instance wrel-of-name (pk (bidi-class-left-to-right)))
        (:instance bidi-name-end-upper-bound)
        (:instance not-bidi-mark-code-point-p-of-nth-of-bidi-name-end)
        (:instance refines-of-bidi-n0-pairs
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (cur (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                    nil
                                                    nil
                                                    ver))
                   (cps name)
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (s (bidi-name-start name ver))
                   (pairs (bidi-bracket-pairs (classes-of name ver)
                                              (roles-of name ver))))
        (:instance take-of-bidi-n0-pairs
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (cur (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                    nil
                                                    nil
                                                    ver))
                   (cps name)
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (s (bidi-name-start name ver))
                   (pairs (bidi-bracket-pairs (classes-of name ver)
                                              (roles-of name ver))))
        (:instance nthcdr-of-bidi-n0-pairs
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (cur (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                    nil
                                                    nil
                                                    ver))
                   (cps name)
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (s (bidi-name-start name ver))
                   (e (bidi-name-end name ver))
                   (pairs (bidi-bracket-pairs (classes-of name ver)
                                              (roles-of name ver))))))

; The class at the end of the middle part.

(defrulel strong-r-p-of-nth-before-bidi-name-end
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (strong-r-p
            (nth (+ -1 (bidi-name-end name ver))
                 (bidi-n0-pairs
                  (bidi-clusters-weak-classes (bidi-clusters name ver)
                                              nil
                                              nil
                                              ver)
                  (classes-of name ver)
                  (bidi-bracket-pairs (classes-of name ver)
                                      (roles-of name ver))
                  sos
                  embedding))))
  :cases ((< (bidi-name-to-last-letter-or-digit name ver)
             (bidi-name-pairs-end (bidi-bracket-pairs (classes-of name ver)
                                                      (roles-of name ver))
                                  name
                                  ver)))
  :disable (kind-of-nth-of-bidi-n0-pairs
            strong-r-p-of-nth-after-last-letter-or-digit
            strong-r-p-of-nth-when-refines
            n0-of-name
            pairs-of-name
            w-ok-of-name
            wrel-of-name)
  :enable (bidi-name-end
           max
           strong-r-p
           bidi-rule-wide-p)
  :use (pairs-of-name
        w-ok-of-name
        n0-of-name
        (:instance wrel-of-name (pk (bidi-class-left-to-right)))
        (:instance bidi-name-end-upper-bound)
        (:instance bidi-name-start-below-len)
        (:instance bidi-name-start-below-bidi-name-to-last-letter-or-digit)
        (:instance kind-of-nth-of-bidi-n0-pairs
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (cur (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                    nil
                                                    nil
                                                    ver))
                   (cps name)
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (s (bidi-name-start name ver))
                   (pairs (bidi-bracket-pairs (classes-of name ver)
                                              (roles-of name ver)))
                   (k (bidi-leading-marks
                       (nthcdr (bidi-name-pairs-end
                                (bidi-bracket-pairs (classes-of name ver)
                                                    (roles-of name ver))
                                name
                                ver)
                               name)
                       ver)))
        (:instance strong-r-p-of-nth-after-last-letter-or-digit
                   (cps name)
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (k (bidi-leading-marks
                       (nthcdr (bidi-name-to-last-letter-or-digit name ver)
                               name)
                       ver)))
        (:instance strong-r-p-of-nth-when-refines
                   (x (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (y (bidi-n0-pairs
                       (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                   nil
                                                   nil
                                                   ver)
                       (classes-of name ver)
                       (bidi-bracket-pairs (classes-of name ver)
                                           (roles-of name ver))
                       sos
                       embedding))
                   (i (+ -1
                         (bidi-name-to-last-letter-or-digit name ver)
                         (bidi-leading-marks
                          (nthcdr (bidi-name-to-last-letter-or-digit name ver)
                                  name)
                          ver))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The levels of the one isolating run sequence of a name.

(defruledl bidi-resolve-sequence-of-name-in-steps
  (implies (and (equal sos (bidi-class-left-to-right))
                (equal eos (bidi-class-left-to-right))
                (equal level 0))
           (equal (bidi-resolve-sequence (classes-of name ver)
                                         (roles-of name ver)
                                         sos
                                         eos
                                         level)
                  (bidi-implicit-levels
                   (bidi-n1-n2
                    (bidi-n0-pairs
                     (bidi-resolve-weak-types (classes-of name ver) sos)
                     (classes-of name ver)
                     (bidi-bracket-pairs (classes-of name ver)
                                         (roles-of name ver))
                     sos
                     sos)
                    sos
                    eos
                    sos)
                   level)))
  :enable (bidi-resolve-sequence
           bidi-resolve-neutral-types
           bidi-n0
           bidi-level-direction))

(defrulel bidi-resolve-weak-types-of-classes-of-name
  (implies (and (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (equal (bidi-class-kind sos) :left-to-right))
           (equal (bidi-resolve-weak-types (classes-of name ver) sos)
                  (bidi-clusters-weak-classes (bidi-clusters name ver)
                                              nil
                                              nil
                                              ver)))
  :use bidi-resolve-weak-types-when-bidi-rule-wide-p)

(defrulel bidi-resolve-sequence-of-name
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (equal sos (bidi-class-left-to-right))
                (equal eos (bidi-class-left-to-right))
                (equal level 0))
           (equal (bidi-resolve-sequence (classes-of name ver)
                                         (roles-of name ver)
                                         sos
                                         eos
                                         level)
                  (bidi-name-levels name ver)))
  :enable bidi-resolve-sequence-of-name-in-steps
  :disable (n0-of-name
            strong-r-p-of-nth-before-bidi-name-end)
  :use ((:instance n0-of-name
                   (sos (bidi-class-left-to-right))
                   (embedding (bidi-class-left-to-right)))
        (:instance strong-r-p-of-nth-before-bidi-name-end
                   (sos (bidi-class-left-to-right))
                   (embedding (bidi-class-left-to-right)))
        weak-classes-of-name
        (:instance levels-of-name-given-n0
                   (n0 (bidi-n0-pairs
                        (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                    nil
                                                    nil
                                                    ver)
                        (classes-of name ver)
                        (bidi-bracket-pairs (classes-of name ver)
                                            (roles-of name ver))
                        (bidi-class-left-to-right)
                        (bidi-class-left-to-right)))
                   (sos (bidi-class-left-to-right))
                   (eos (bidi-class-left-to-right))
                   (embedding (bidi-class-left-to-right))
                   (level 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The classes of a name are plain, and rule L1 changes no level.

(defrulel bidi-plain-class-listp-of-classes-of
  (implies (bidi-rule-wide-code-points-p name ver)
           (bidi-plain-class-listp (classes-of name ver)))
  :induct (len name)
  :enable (len
           classes-of
           bidi-rule-wide-code-point-p
           bidi-plain-class-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(local
 (define no-space-p (classes)
   :returns (yes/no booleanp)
   (or (atom classes)
       (and (not (member-eq (bidi-class-kind (car classes))
                            '(:segment-separator :white-space)))
            (no-space-p (cdr classes))))
   :verify-guards nil
   :hooks nil))

(defrulel no-space-p-of-classes-of
  (implies (bidi-rule-wide-code-points-p name ver)
           (no-space-p (classes-of name ver)))
  :induct (len name)
  :enable (len
           classes-of
           no-space-p
           bidi-rule-wide-code-point-p))

(defrulel bidi-reset-plain-when-no-space-p
  (implies (and (no-space-p classes)
                (nat-listp levels)
                (equal (len levels) (len classes)))
           (equal (mv-nth 0 (bidi-reset-plain classes levels))
                  levels))
  :induct (two-lists-induction classes levels)
  :enable (two-lists-induction
           bidi-reset-plain
           no-space-p
           len))

(defrulel len-of-bidi-name-levels-when-wide
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (equal (len (bidi-name-levels name ver))
                  (len name)))
  :disable (bidi-resolve-sequence-of-name
            len-of-bidi-resolve-sequence)
  :use ((:instance bidi-resolve-sequence-of-name
                   (sos (bidi-class-left-to-right))
                   (eos (bidi-class-left-to-right))
                   (level 0))
        (:instance len-of-bidi-resolve-sequence
                   (classes (classes-of name ver))
                   (roles (roles-of name ver))
                   (sos (bidi-class-left-to-right))
                   (eos (bidi-class-left-to-right))
                   (level 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A paragraph from right to left: the paragraph embedding level is 1,
; and the direction at the two ends of the sequence is R.
; This part is for a name whose first code point is not a mark.

; Rule N0 still only changes some classes ON to R:
; no class L is inside a pair, so each pair is set to R or left as it is.

(defrulel refines-of-bidi-n0-pair-when-embedding-is-right-to-left
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (pair-fit x cps s ver)
                (equal embedding (bidi-class-right-to-left)))
           (refines w
                    (bidi-n0-pair cur
                                  (classes-of cps ver)
                                  x
                                  sos
                                  embedding)))
  :enable (bidi-n0-pair
           w-ok
           pair-fit)
  :disable (not-bidi-n0-strong-inside-p-when-no-l-from
            refines-of-nthcdr
            no-l-when-refines
            refines-of-bidi-n0-set-pair
            refines-transitive)
  :use ((:instance not-bidi-n0-strong-inside-p-when-no-l-from
                   (classes cur)
                   (k s)
                   (position 0)
                   (pair x)
                   (direction (bidi-class-left-to-right)))
        (:instance refines-of-nthcdr (x w) (y cur) (n s))
        (:instance no-l-when-refines
                   (x (nthcdr s w))
                   (y (nthcdr s cur)))
        (:instance refines-of-bidi-n0-set-pair
                   (position 0)
                   (pair x)
                   (direction (bidi-class-right-to-left))
                   (after nil))
        (:instance refines-transitive
                   (x w)
                   (y cur)
                   (z (bidi-n0-set-pair cur
                                        (classes-of cps ver)
                                        0
                                        x
                                        (bidi-class-right-to-left)
                                        nil)))))

(defrulel refines-of-bidi-n0-pairs-when-embedding-is-right-to-left
  (implies (and (w-ok w s)
                (wrel cps w pk carry ver)
                (refines w cur)
                (pairs-fit pairs cps s ver)
                (equal embedding (bidi-class-right-to-left)))
           (refines w
                    (bidi-n0-pairs cur
                                   (classes-of cps ver)
                                   pairs
                                   sos
                                   embedding)))
  :induct (bidi-n0-pairs cur (classes-of cps ver) pairs sos embedding)
  :enable (bidi-n0-pairs
           pairs-fit))

; Rules N1 and N2 give the class R to every class ON
; of a list of classes without L,
; when the direction is R before it, after it and for the embedding.

(defrulel bidi-neutral-run-end-when-mid-p
  (implies (and (mid-p x)
                (equal eos (bidi-class-right-to-left)))
           (equal (bidi-neutral-run-end x eos)
                  (bidi-class-right-to-left)))
  :induct (len x)
  :enable (len
           mid-p
           bidi-neutral-run-end
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction))

(defrulel bidi-n1-n2-when-mid-p
  (implies (and (mid-p x)
                (equal previous (bidi-class-right-to-left))
                (equal eos (bidi-class-right-to-left))
                (equal embedding (bidi-class-right-to-left)))
           (equal (bidi-n1-n2 x previous eos embedding)
                  (to-r x)))
  :induct (len x)
  :enable (len
           mid-p
           to-r
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((:free (p s e) (bidi-n1-n2 x p s e))))

; The implicit levels at level 1: 1 for the class R, 2 for AN and EN.

(defrulel bidi-implicit-levels-of-to-r-at-level-1
  (implies (and (mid-p m)
                (equal level 1))
           (equal (bidi-implicit-levels (to-r m) level)
                  (lev m)))
  :induct (len m)
  :enable (len
           mid-p
           to-r
           lev
           bidi-implicit-level)
  :expand ((:free (a b) (bidi-implicit-levels (cons a b) 1))
           (bidi-implicit-levels nil 1)))

; The levels of the one isolating run sequence of the name.

(defruledl bidi-resolve-sequence-of-name-in-steps-at-level-1
  (implies (and (equal sos (bidi-class-right-to-left))
                (equal eos (bidi-class-right-to-left))
                (equal level 1))
           (equal (bidi-resolve-sequence (classes-of name ver)
                                         (roles-of name ver)
                                         sos
                                         eos
                                         level)
                  (bidi-implicit-levels
                   (bidi-n1-n2
                    (bidi-n0-pairs
                     (bidi-resolve-weak-types (classes-of name ver) sos)
                     (classes-of name ver)
                     (bidi-bracket-pairs (classes-of name ver)
                                         (roles-of name ver))
                     sos
                     sos)
                    sos
                    eos
                    sos)
                   level)))
  :enable (bidi-resolve-sequence
           bidi-resolve-neutral-types
           bidi-n0
           bidi-level-direction))

(defrulel bidi-resolve-weak-types-of-classes-of-name-after-right-to-left
  (implies (and (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (not (bidi-mark-code-point-p (car name) ver))
                (equal (bidi-class-kind sos) :right-to-left))
           (equal (bidi-resolve-weak-types (classes-of name ver) sos)
                  (bidi-clusters-weak-classes (bidi-clusters name ver)
                                              nil
                                              nil
                                              ver)))
  :use bidi-resolve-weak-types-when-bidi-rule-wide-p-after-right-to-left)

(defrulel bidi-resolve-sequence-of-name-at-level-1
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (not (bidi-mark-code-point-p (car name) ver))
                (equal sos (bidi-class-right-to-left))
                (equal eos (bidi-class-right-to-left))
                (equal level 1))
           (equal (bidi-resolve-sequence (classes-of name ver)
                                         (roles-of name ver)
                                         sos
                                         eos
                                         level)
                  (bidi-middle-levels (bidi-clusters name ver) nil ver)))
  :enable (bidi-resolve-sequence-of-name-in-steps-at-level-1
           bidi-rule-wide-p)
  :disable (pairs-of-name
            w-ok-of-name
            wrel-of-name
            refines-of-bidi-n0-pairs-when-embedding-is-right-to-left)
  :use (pairs-of-name
        w-ok-of-name
        (:instance wrel-of-name (pk (bidi-class-left-to-right)))
        (:instance refines-of-bidi-n0-pairs-when-embedding-is-right-to-left
                   (w (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                  nil
                                                  nil
                                                  ver))
                   (cur (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                    nil
                                                    nil
                                                    ver))
                   (cps name)
                   (pk (bidi-class-left-to-right))
                   (carry nil)
                   (s (bidi-name-start name ver))
                   (pairs (bidi-bracket-pairs (classes-of name ver)
                                              (roles-of name ver)))
                   (sos (bidi-class-right-to-left))
                   (embedding (bidi-class-right-to-left)))))

; Rule L1 changes no level: the name has no separator, no white space,
; and no character that rule X9 removes.

(local
 (define no-reset-p (classes)
   :returns (yes/no booleanp)
   (or (atom classes)
       (and (not (member-eq (bidi-class-kind (car classes))
                            '(:segment-separator
                              :paragraph-separator
                              :white-space)))
            (not (bidi-class-isolate-formatting-p (car classes)))
            (not (bidi-class-removed-p (car classes)))
            (no-reset-p (cdr classes))))
   :verify-guards nil
   :hooks nil))

(defrulel no-reset-p-of-classes-of
  (implies (bidi-rule-wide-code-points-p name ver)
           (no-reset-p (classes-of name ver)))
  :induct (len name)
  :enable (len
           classes-of
           no-reset-p
           bidi-rule-wide-code-point-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel bidi-reset-all-levels-when-no-reset-p
  (implies (and (no-reset-p classes)
                (nat-listp levels)
                (equal (len levels) (len classes)))
           (equal (mv-nth 0 (bidi-reset-all-levels classes
                                                   levels
                                                   paragraph-level))
                  levels))
  :induct (two-lists-induction classes levels)
  :enable (two-lists-induction
           bidi-reset-all-levels
           no-reset-p
           len))

(defrulel len-of-bidi-middle-levels-of-name
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (not (bidi-mark-code-point-p (car name) ver)))
           (equal (len (bidi-middle-levels (bidi-clusters name ver) nil ver))
                  (len name)))
  :disable (bidi-resolve-sequence-of-name-at-level-1
            len-of-bidi-resolve-sequence)
  :use ((:instance bidi-resolve-sequence-of-name-at-level-1
                   (sos (bidi-class-right-to-left))
                   (eos (bidi-class-right-to-left))
                   (level 1))
        (:instance len-of-bidi-resolve-sequence
                   (classes (classes-of name ver))
                   (roles (roles-of name ver))
                   (sos (bidi-class-right-to-left))
                   (eos (bidi-class-right-to-left))
                   (level 1))))

(defrulel bidi-paragraph-all-levels-at-level-1-when-code-point-listp
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver)
                (not (bidi-mark-code-point-p (car name) ver)))
           (equal (bidi-paragraph-all-levels (code-points-to-bidi-chars name
                                                                        ver)
                                             1)
                  (bidi-middle-levels (bidi-clusters name ver) nil ver)))
  :enable (bidi-paragraph-all-levels-when-plain-at-level
           bidi-rule-wide-p
           bidi-level-direction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems of this book.

(defrulel bidi-paragraph-all-levels-when-code-point-listp
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver)
                (bidi-right-to-left-label-p name ver))
           (equal (bidi-paragraph-all-levels (code-points-to-bidi-chars name
                                                                        ver)
                                             0)
                  (bidi-name-levels name ver)))
  :enable (bidi-paragraph-all-levels-when-plain
           bidi-rule-wide-p))

(defsection bidi-rule-display-levels
  :parents (bidi-rule-display)
  :short "Theorems that the Unicode Bidirectional Algorithm
          gives the levels of @(tsee bidi-name-levels),
          in a paragraph from left to right,
          to a name that satisfies the wide rule
          and has a right-to-left letter or an Arabic digit,
          and those of @(tsee bidi-middle-levels) for the whole name
          in a paragraph from right to left."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second argument of @(tsee bidi-paragraph-all-levels)
     is the paragraph embedding level,
     which is 0 in a paragraph from left to right.
     The name is the whole paragraph.")
   (xdoc::p
    "The proof follows the algorithm rule by rule.
     The classes after the weak rules, W1 to W7 of [UAX #9],
     are known (see @(see bidi-rule-display-weak)).
     Rule N0, on the bracket pairs,
     changes some classes @('ON') (@('Other_Neutral'))
     to @('R') (@('Right_To_Left')), all in the middle part of the name;
     this needs the fact that no two bracket pairs cross,
     which is the theorem
     @('bidi-pairs-nested-p-of-bidi-bracket-pairs').
     Rules N1 and N2 give the direction of the paragraph
     to what is before and after the middle part,
     and @('R') to every @('ON') of the middle part.
     The levels are then 0 outside the middle part
     and, in it, 2 for the classes @('AN') (@('Arabic_Number'))
     and @('EN') (@('European_Number')) and 1 for @('R')
     [UAX #9, rules I1 and I2].
     The rule is disabled by default.")
   (xdoc::p
    "The second theorem is for a paragraph from right to left,
     where the paragraph embedding level is 1,
     and for a name whose first character is not a mark.
     The classes after the weak rules are then the same.
     Rule N0 again changes some classes @('ON') to @('R')
     and nothing else,
     and rules N1 and N2 give @('R') to every @('ON') that is left,
     since the direction is @('R') at the two ends of the name.
     So no character has level 0:
     the levels are 2 for @('AN') and @('EN') and 1 for @('R'),
     which is what @(tsee bidi-middle-levels) gives
     for the clusters of the whole name.
     For a label that satisfies the strict rule
     these are the levels of the first theorem
     (see @(see bidi-rule-display-strict-theorem)).
     This rule is disabled by default too."))

  (defruled bidi-paragraph-all-levels-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name ver)
                  (bidi-right-to-left-label-p name ver))
             (equal (bidi-paragraph-all-levels
                     (code-points-to-bidi-chars name ver)
                     0)
                    (bidi-name-levels name ver)))
    :use (:instance bidi-paragraph-all-levels-when-code-point-listp
                    (name (code-point-list-fix name))))

  (defruled bidi-paragraph-all-levels-at-level-1-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name ver)
                  (bidi-right-to-left-label-p name ver)
                  (not (bidi-mark-code-point-p (car name) ver)))
             (equal (bidi-paragraph-all-levels
                     (code-points-to-bidi-chars name ver)
                     1)
                    (bidi-middle-levels (bidi-clusters name ver) nil ver)))
    :use (:instance bidi-paragraph-all-levels-at-level-1-when-code-point-listp
                    (name (code-point-list-fix name)))))
