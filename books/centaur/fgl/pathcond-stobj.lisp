; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>
 
(in-package "FGL")

(include-book "pathcond-aignet")
(include-book "aig-pathcond-stobj")
(include-book "centaur/ubdds/lite" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(acl2::defstobj-clone aignet-pathcond aignet::aignet-pathcond
  :strsubst (("abcd" . "abcd")) :pkg fgl-package)

(defstobj pathcond
  (pathcond-bdd :type (satisfies acl2::ubddp) :initially t)
  (pathcond-aig :type calist-stobj)
  (pathcond-aignet :type aignet-pathcond)
  (pathcond-enabledp :type (member t nil) :initially t)
  (pathcond-checkpoint-ptrs :type (satisfies nat-listp) :initially nil)
  (pathcond-checkpoint-ubdds :type (satisfies acl2::ubdd-listp) :initially nil))



(define pathcond-init (pathcond)
  :prepwork ((local (defthm equal-of-len
                      (implies (syntaxp (quotep n))
                               (equal (equal (len x) n)
                                      (cond ((not (natp n)) nil)
                                            ((equal n 0) (not (consp x)))
                                            (t (and (Consp x)
                                                    (equal (len (cdr x)) (1- n))))))))))
  :guard-hints (("goal" :in-theory (enable update-nth)))
  :enabled t
  (mbe :logic (non-exec (create-pathcond))
       :exec (b* ((pathcond (update-pathcond-bdd t pathcond))
                  (pathcond (update-pathcond-enabledp t pathcond))
                  (pathcond (update-pathcond-checkpoint-ptrs nil pathcond))
                  (pathcond (update-pathcond-checkpoint-ubdds nil pathcond)))
               (stobj-let ((calist-stobj (pathcond-aig pathcond))
                           (aignet-pathcond (pathcond-aignet pathcond)))
                          (calist-stobj aignet-pathcond)
                          (b* ((calist-stobj (calist-stobj-empty calist-stobj))
                               (aignet-pathcond (aignet-pathcond-rewind 0 aignet-pathcond)))
                            (mv calist-stobj aignet-pathcond))
                          pathcond))))
