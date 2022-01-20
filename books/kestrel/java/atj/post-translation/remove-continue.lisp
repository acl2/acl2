; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../java-syntax-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-remove-continue
  :parents (atj-post-translation)
  :short "Post-translation step:
          remove unnecessary @('continue') statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "atj-post-translation-tailrec-elimination"
                    "tail recursion elimination step")
    " produces loops where the recursive calls are replaced with
     @('continue') statements.
     However, when one of these statements
     is the last thing executed in the loop body,
     it is superfluous and can be removed.")
   (xdoc::p
    "This post-translation step performs this removal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-ending-continue ((block jblockp))
  :returns (new-block jblockp :hyp :guard)
  :verify-guards :after-returns
  :short "Remove any ending @('continue') statements
          from a block that forms a loop body."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on bodies of loops (which are blocks).
     It removes any ending @('continue'),
     including the ones inside the branches of ending @('if')s,
     recursively.")
   (xdoc::p
    "If the block is empty, we return it unchanged.
     If the block ends with @('continue'),
     we return the block without that last statement.
     If the block ends with @('if') (with or without @('else')),
     we recursively process the branch(es).")
   (xdoc::p
    "We prove that the size of the new block is not greater than
     the size of the original block.
     This is used to prove the termination of
     @(tsee atj-remove-continue-in-jstatem) and
     @(tsee atj-remove-continue-in-jblock)."))
  (b* (((when (endp block)) nil)
       (last-statem (car (last block)))
       (butlast-block (butlast block 1)))
    (case (jstatem-kind last-statem)
      (:continue butlast-block)
      (:if (append butlast-block
                   (list (jstatem-if (jstatem-if->test last-statem)
                                     (atj-remove-ending-continue
                                      (jstatem-if->then last-statem))))))
      (:ifelse (append butlast-block
                       (list
                        (jstatem-ifelse (jstatem-ifelse->test last-statem)
                                        (atj-remove-ending-continue
                                         (jstatem-ifelse->then last-statem))
                                        (atj-remove-ending-continue
                                         (jstatem-ifelse->else last-statem))))))
      (otherwise block)))
  :measure (jblock-count-ifs block)
  ///

  (defruledl atj-remove-ending-continue-does-not-increase-size-lemma-1
    (implies (and (consp block)
                  (jstatem-case (car (last block)) :if))
             (equal (jblock-count block)
                    (+ 4
                       (jblock-count (butlast block 1))
                       (jblock-count (jstatem-if->then (car (last block)))))))
    :enable (jblock-count jstatem-count))

  (defruled atj-remove-ending-continue-does-not-increase-size-lemma-2
    (implies
     (and (consp block)
          (jstatem-case (car (last block)) :ifelse))
     (equal (jblock-count block)
            (+ 5
               (jblock-count (butlast block 1))
               (jblock-count (jstatem-ifelse->then (car (last block))))
               (jblock-count (jstatem-ifelse->else (car (last block)))))))
    :enable (jblock-count jstatem-count))

  (defret atj-remove-ending-continue-does-not-increase-size
    (<= (jblock-count (atj-remove-ending-continue block))
        (jblock-count block))
    :rule-classes :linear
    :hints (("Goal" :in-theory (e/d (atj-remove-ending-continue
                                     jblock-count
                                     jstatem-count)
                                    (butlast)))
            '(:use
              (atj-remove-ending-continue-does-not-increase-size-lemma-1
               atj-remove-ending-continue-does-not-increase-size-lemma-2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-remove-continue-in-jstatems+jblocks
  :short "Remove the ending @('continue') statements
          in all the loops found in statements and blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "We recursively process all the statements and blocks.
     When we encounter a loop,
     we use @(tsee atj-remove-ending-continue)
     to remove all its ending @('continue')s (if any),
     and then we recursively process the resulting body
     in order to remove @('continue')s from any nested loops.")
   (xdoc::p
    "Currently ATJ's ACL2-to-Java translation does not generate nested loops,
     and none of ATJ's post-translation steps generates nested loops.
     However, making this post-translation step more general
     require only little additional effort."))

  (define atj-remove-continue-in-jstatem ((statem jstatemp))
    :returns (new-statem jstatemp :hyp :guard)
    (jstatem-case
     statem
     :locvar statem
     :expr statem
     :return statem
     :throw statem
     :break statem
     :continue statem
     :if (jstatem-if statem.test
                     (atj-remove-continue-in-jblock statem.then))
     :ifelse (jstatem-ifelse statem.test
                             (atj-remove-continue-in-jblock statem.then)
                             (atj-remove-continue-in-jblock statem.else))
     :while (b* ((body (atj-remove-ending-continue statem.body)))
              (jstatem-while statem.test
                             (atj-remove-continue-in-jblock body)))
     :do (b* ((body (atj-remove-ending-continue statem.body)))
           (jstatem-do (atj-remove-continue-in-jblock body)
                       statem.test))
     :for (b* ((body (atj-remove-ending-continue statem.body)))
            (jstatem-for statem.init
                         statem.test
                         statem.update
                         (atj-remove-continue-in-jblock body))))
    :measure (jstatem-count statem))

  (define atj-remove-continue-in-jblock ((block jblockp))
    :returns (new-block jblockp :hyp :guard)
    (cond ((endp block) nil)
          (t (cons (atj-remove-continue-in-jstatem (car block))
                   (atj-remove-continue-in-jblock (cdr block)))))
    :measure (jblock-count block))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-remove-continue-in-jstatem))
