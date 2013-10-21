;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "mksym")

;; The defthms-flag macro
;;
;; We now introduce a macro which helps prove theorems about mutually recursive
;; functions using a flag function.  The general form is:
;;
;;   (defthms-flag
;;     :shared-hyp (and hyp1 ... hypK)
;;     :thms ((flag1 name1 thm1) ... (flagN nameN thmN) (t nameElse thmElse))
;;     :flag-var var
;;     :hints (("Goal" ...)))
;;
;; Calling this will introduce an encapsulate event which essentially has
;; the following shape:
;;
;;    (encapsulate
;;     ()
;;     (local (defthm lemma
;;              (implies shared-hyp
;;                       (cond ((equal var 'flag1)
;;                              thm1)
;;                             ((equal var 'flag2)
;;                              thm2)
;;                             ...
;;                             ((equal var 'flagN)
;;                              thmN)
;;                             (t
;;                              thmElse)))
;;              :rule-classes nil
;;              :hints (("Goal" ...))))
;;
;;     (defthm name1
;;       (implies shared-hyp
;;                thm1)
;;       :hints(("Goal" :use ((:instance lemma (flag 'flag1))))))
;;
;;     ...
;;
;;     (defthm nameN
;;       (implies shared-hyp
;;                thmN)
;;       :hints(("Goal" :use ((:instance lemma (flag 'flagN))))))
;;
;;     (defthm nameElse
;;       (implies shared-hyp
;;                thmElse)
;;       :hints(("Goal" :use ((:instance lemma (flag 'defthms-flag-otherwise)))))))
;;
;; By default, flag-var is set to "flag" and shared-hyp is set to t.
;;
;; The flags in the (flag name thm) triples need not be distinct; all such
;; triples with the same flags will be merged together in the cond.

(defun flag-triplep (x)
  (declare (xargs :mode :program))
  (and (or (and (true-listp x)
                (equal (length x) 3))
           (er hard 'flag-triplep "Expected ~x0 to be a (flag name thm) triple.~%" x))
       (or (symbolp (first x))
           (er hard 'flag-triplep "Expected the flag, ~x0, to be a symbol.~%" x))
       (or (symbolp (second x))
           (er hard 'flag-triplep "Expected the name, ~x0, to be a symbol.~%" x))
       ;; No checking of the theorem.
       ))

(defun flag-triple-listp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (flag-triplep (car x))
           (flag-triple-listp (cdr x)))
    t))


;; We sort the flag-triple we're given into buckets by their flag.  Each bucket
;; has the form (flag <flag-triple-list>)

(defun add-flag-triple-to-proper-bucket (flag-triple buckets)
  (declare (xargs :mode :program))
  (if (consp buckets)
      (let* ((bucket1         (car buckets))
             (bucket1-flag    (first bucket1))
             (bucket1-triples (second bucket1)))
        (if (equal bucket1-flag (car flag-triple))
            (let ((new-bucket1 (list bucket1-flag (cons flag-triple bucket1-triples))))
              (cons new-bucket1 (cdr buckets)))
          (cons bucket1 (add-flag-triple-to-proper-bucket flag-triple (cdr buckets)))))
    (let* ((new-bucket-tag     (car flag-triple))
           (new-bucket-triples (list flag-triple))
           (new-bucket         (list new-bucket-tag new-bucket-triples)))
      (list new-bucket))))

(defun assign-flag-triples-to-buckets (flag-triples buckets)
  (declare (xargs :mode :program))
  (if (consp flag-triples)
      (assign-flag-triples-to-buckets (cdr flag-triples)
                                      (add-flag-triple-to-proper-bucket (car flag-triples) buckets))
    buckets))


;; We also hyps the hyps that are shared on a per-flag basis.

(defun eliminate-all-forcing (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (member-equal (car x) '(force MILAWA::force))
          (eliminate-all-forcing (cadr x))
        (cons (eliminate-all-forcing (car x))
              (eliminate-all-forcing (cdr x))))
    x))

(defun split-into-hyps-and-conclusions (thms)
  (declare (xargs :mode :program))
  ;; Thms are a list we want to prove, which share a particular flag.
  ;; We recognize theorems of three forms:
  ;;   1. (implies (and hyp1 ... hypN) concl)
  ;;   2. (implies hyp concl)
  ;;   3. concl
  ;; We create a new list whose entries are pairs of the form (hyp-list . concl)
  (if (consp thms)
      (cons (let ((thm1 (car thms)))
              (if (and (consp thm1)
                       (equal (first thm1) 'implies)
                       (equal (length thm1) 3))
                  (let ((antecedent (second thm1))
                        (consequent (third thm1)))
                    (if (and (consp antecedent)
                             (equal (first antecedent) 'and))
                        ;; (implies (and hyp1 ... hypN) concl)
                        (cons (cdr antecedent) consequent)
                      ;; (implies hyp1 concl)
                      (cons (list antecedent) consequent)))
                ;; concl
                (cons nil thm1)))
            (split-into-hyps-and-conclusions (cdr thms)))
    nil))

;; We compute the intersection of these hyp-lists to identify the shared hyps.

(defun intersect (x y)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (member-equal (car x) y)
          (cons (car x) (intersect (cdr x) y))
        (intersect (cdr x) y))
    nil))

(defun intersect-list (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (consp (cdr x))
          (intersect (car x) (intersect-list (cdr x)))
        (car x))
    nil))


;; We then alter the (hyp-list . concl)-pairs list by removing all the shared
;; hyps from each hyp-list.

(defun aux-consolidate-theorems (thms shared-hyps)
  ;; thms is a list of (hyp-list . concl) pairs.  We turn it into a list of
  ;; (implies remaining-hyps concl) where the remaining-hyps are the original
  ;; hyps, minus the shared hyps.
  (declare (xargs :mode :program))
  (if (consp thms)
      (let* ((thm1       (car thms))
             (thm1-hyps  (car thm1))
             (thm1-concl (cdr thm1))
             (new-hyps   (set-difference-equal thm1-hyps shared-hyps)))
        (cons (cond ((and (consp new-hyps)
                          (consp (cdr new-hyps)))
                     `(if (and ,@new-hyps) ,thm1-concl t))
                    ((consp new-hyps)
                     `(if ,(car new-hyps) ,thm1-concl t))
                    (t
                     thm1-concl))
              (aux-consolidate-theorems (cdr thms) shared-hyps)))
    nil))

(defun consolidate-theorems (thms)
  (declare (xargs :mode :program))
  ;; Thms are the ACL2-style theorems for a single flag.  We compute the shared
  ;; hyps and create the best theorem we can.
  (if (atom (cdr thms))
      ;; Only one theorem.  Don't bother consolidating anything.
      (car thms)
    ;; More than one theorem.  Try to consolidate.
    (let* ((hyp/conc-list (split-into-hyps-and-conclusions thms))
           (shared-hyps   (intersect-list (strip-cars hyp/conc-list)))
           (tweaked-thms  (aux-consolidate-theorems hyp/conc-list shared-hyps)))
      (cond ((and (consp shared-hyps)
                  (consp (cdr shared-hyps)))
             `(implies (and ,@shared-hyps)
                       (and ,@tweaked-thms)))
            ((consp shared-hyps)
             `(implies ,(car shared-hyps)
                       (and ,@tweaked-thms)))
            (t
             `(and ,@tweaked-thms))))))

(defun create-cond-pairs-from-buckets1 (flag-var buckets)
  (declare (xargs :mode :program))
  (if (consp buckets)
      (let* ((bucket1         (car buckets))
             (bucket1-flag    (first bucket1))
             (bucket1-triples (second bucket1))
             (bucket1-thms    (strip-caddrs bucket1-triples)))
        (cons `(,(if (equal bucket1-flag t)
                     t
                   `(equal ,flag-var ',bucket1-flag))
                ,(consolidate-theorems (eliminate-all-forcing bucket1-thms)))
              (create-cond-pairs-from-buckets1 flag-var (cdr buckets))))
    nil))

(defun create-cond-pairs-from-buckets (flag-var buckets)
  (declare (xargs :mode :program))
  (let ((main-cond-pairs (create-cond-pairs-from-buckets1 flag-var buckets)))
    (if (assoc t buckets)
        ;; Some bucket has t as its flag, so we don't need to bother with a
        ;; phony case.
        main-cond-pairs
      (append main-cond-pairs `((t t))))))

(defun create-named-theorem-from-triple (flag-triple shared-hyp flag-var atp lemma-name)
  (declare (xargs :mode :program))
  (let* ((flag  (first flag-triple))
         (name  (second flag-triple))
         (thm   (third flag-triple))
         (event (if atp 'MILAWA::defthm@ 'MILAWA::defthm))
         (thm*  (if (equal shared-hyp t)
                    thm
                  `(implies ,shared-hyp ,thm))))
    `(,event ,name
             ,thm*
             :hints(("Goal" :use ((:instance ,lemma-name (,flag-var ',(if (equal flag t)
                                                                          'MILAWA::defthms-flag-otherwise
                                                                        flag)))))))))

(defun create-named-theorems-from-triples (flag-triples shared-hyp flag-var atp lemma-name)
  (declare (xargs :mode :program))
  (if (consp flag-triples)
      (cons (create-named-theorem-from-triple (car flag-triples) shared-hyp flag-var atp lemma-name)
            (create-named-theorems-from-triples (cdr flag-triples) shared-hyp flag-var atp lemma-name))
    nil))

(defun defthms-flag-fn (triples shared-hyp flag-var hints atp)
  (declare (xargs :mode :program))
  (and (flag-triple-listp triples)
       (let* ((buckets    (assign-flag-triples-to-buckets triples nil))
              (event      (if atp 'MILAWA::defthm@ 'MILAWA::defthm))
              (lemma-name (mksym 'lemma-for- (second (car triples))))
              (flag-thm   (if (equal shared-hyp t)
                              `(cond ,@(create-cond-pairs-from-buckets flag-var buckets))
                            `(implies ,shared-hyp
                                      (cond ,@(create-cond-pairs-from-buckets flag-var buckets))))))
         `(encapsulate
           ()
           (,event ,lemma-name
                   ,flag-thm
                   :rule-classes nil
                   :hints ,hints)
           ,@(create-named-theorems-from-triples triples shared-hyp flag-var atp lemma-name)))))

(defmacro MILAWA::defthms-flag (&key (shared-hyp 't) thms (flag-var 'MILAWA::flag) @contextp hints)
  (defthms-flag-fn thms shared-hyp flag-var hints @contextp))

