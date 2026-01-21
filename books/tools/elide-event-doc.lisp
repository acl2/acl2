; Copyright (C) 2025, ForrestHunt, Inc.
; Written by Matt Kaufmann, December, 2025
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc elide-event
  :parents (macro-libraries)
  :short "Remove parts of an event that are unnecessary on a second pass"
  :long "<p>This relatively advanced utility is useful when creating an event
 to be evaluated only during the second pass of an @(tsee encapsulate) or
 @(tsee include-book) event.  The usage is</p>

 @({
 (elide-event ev)
 })

 <p>where @('ev') is a legal event, which might typically be obtained using
 @(tsee get-event).  The example below illustrates its use, but is rather
 contrived.  A more serious use of @('elide-event') is made by the utility,
 @(tsee with-supporters).</p>

 <h3>(Contrived) Example</h3>

 <p>The @(see community-book) @('centaur/misc/nth-equiv.lisp') introduces the
 function @('nth-equiv') as shown below.  It then introduces the function
 @('nth-equiv-exec') as follows.</p>

 @({
 (defun nth-equiv-exec (x y)
   (declare (xargs :guard (and (true-listp x) (true-listp y))
                   :guard-hints ((\"goal\" 
                                  :in-theory
                                  (enable nth-equiv-recursive nth-equiv-exec)))))
   (mbe :logic (nth-equiv x y)
        :exec (or (and (atom x) (atom y))
                  (and (equal (car x) (car y))
                       (nth-equiv-exec (cdr x) (cdr y))))))
 })

 <p>The following @('encapsulate') event introduces @('nth-equiv-exec'), but
 without the @(':guard-hints') above.</p>

 @({
 (encapsulate
   ()
   (local (include-book \"centaur/misc/nth-equiv\" :dir :system))
   ;; The following are redundant on the first pass:
   (defun-sk nth-equiv (x y)
     (forall n (and (equal (nth n x) (nth n y)))))
   (make-event (elide-event (get-event 'nth-equiv-exec (w state)))))
 })

 <p>This works out because on the first pass of the @('encapsulate') event,
 removal of that hint does not affect redundancy, and on the second pass, the
 definition of @('nth-equiv-exec') does not need any sort of hints since proofs
 are skipped.</p>

 <p>The @(tsee xargs) keywords that are eliminated are @(':guard-hints'),
 @(':guard-debug'), @(':hints'), @(':measure-debug'), and @(':otf-flg').  The
 @('comment') declaration is also eliminated.</p>")





(defpointer elide-event-lst elide-event)
