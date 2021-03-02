; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")

(include-book "../mods/svmods")

(fty::defmap svtv-namemap :key-type svar :val-type stringp :true-listp t
  :parents (svtv-steps)
  :short "A mapping from user-provided names (generally symbols) to signal
names in SystemVerilog hierarchical syntax (strings)."
  :long "<p>See @(see svtv-namemap->lhsmap).</p>")

(fty::defmap svtv-name-lhs-map :key-type svar :val-type lhs :true-listp t
  :parents (svtv-steps)
  :short "Mapping from user-provided names (generally symbols) to normalized internal names."
  :long "<p>See @(see svtv-namemap->lhsmap).</p>"
  ///
  (local (defthm svar-p-when-lookup
           (implies (and (svtv-name-lhs-map-p x)
                         (hons-assoc-equal key x))
                    (svar-p key))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-p
                                             hons-assoc-equal)))))
  ;; (defthm svtv-name-lhs-map-p-of-fal-extract
  ;;   (implies (svtv-name-lhs-map-p x)
  ;;            (svtv-name-lhs-map-p (fal-extract keys x)))
  ;;   :hints(("Goal" :in-theory (enable fal-extract))))
  )


(defprod base-fsm
  ((values svex-alist-p
            "Functions of internal signals of the design, using canonical
             names as input and output variables.")
   (nextstate svex-alist-p
               "Next-state functions for stateholding signals.  No variable should
                be both a key of updates and nextstates -- usually the nextstate
                keys have delay values in their names and the updates keys
                don't.")))


(defprod svtv-fsm
  ((base-fsm base-fsm-p)
   ;; (design design-p
   ;;         "Original design from which the FSM was derived.")
   ;; (user-names svtv-namemap-p
   ;;             "Mapping for signal names given by the user.")
   (namemap svtv-name-lhs-map-p
            "Processed name map giving the canonical LHS of each name."))
  :extra-binder-names (values nextstate renamed-values renamed-fsm))

(define svtv-fsm->values ((x svtv-fsm-p))
  :enabled t
  (base-fsm->values (svtv-fsm->base-fsm x)))

(define svtv-fsm->nextstate ((x svtv-fsm-p))
  :enabled t
  (base-fsm->nextstate (svtv-fsm->base-fsm x)))


