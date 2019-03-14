; GL - A Symbolic Simulation Framework for ACL2
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


(include-book "tools/templates" :dir :system)

(progn

  (defconst *scratchobj-types*
    '((:gl-obj gl-object-p gl-object-fix 0)
      (:gl-objlist gl-objectlist-p gl-objectlist-fix 1)
      (:bfr t nil 2)
      (:bfrlist true-listp llist-fix 3 :rule-classes :type-prescription)
      (:cinst constraint-instance-p constraint-instance-fix 4)
      (:cinstlist constraint-instancelist-p constraint-instancelist-fix 5)))


  (defun scratchobj-tmplsubst (tuple lastp)
    (declare (xargs :mode :program))
    (b* (((list* kind pred fix code ruleclasses) tuple))
      (acl2::make-tmplsubst :atoms `((:<kind> . ,kind)
                                     (:<kindcase> . ,(if lastp t kind))
                                     (<codecase> . ,(if lastp t code))
                                     (<pred> . ,pred)
                                     (<fix> . ,fix)
                                     (<code> . ,code)
                                     (<ruleclass> . ,ruleclasses))
                            :strs `(("<KIND>" . ,(symbol-name kind)))
                            :pkg-sym 'fgl::foo
                            :features (and (eq pred t) '(:no-pred)))))
  
  (defun scratchobj-tmplsubsts (tuples)
    (declare (xargs :mode :program))
    (if (atom tuples)
        nil
      (cons (scratchobj-tmplsubst (car tuples) (atom (cdr tuples)))
            (scratchobj-tmplsubsts (cdr tuples)))))

  (defconst *scratchobj-tmplsubsts*
    (scratchobj-tmplsubsts *scratchobj-types*)))
