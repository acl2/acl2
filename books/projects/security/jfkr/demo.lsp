; Copyright David Rager 2006

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

(ld "package.lsp")

(in-package "JFKR")

(include-book "jfkr")

(defconst *1-step-run-ex*
  (mv-let (x y z)
          (run-1-step-honest nil 
                             *initiator-constants* 
                             *responder-constants* 
                             *public-constants* 
                             nil
                             nil)
          (list x y z)))
          
*1-step-run-ex*


(defconst *2-step-run-ex*
  (mv-let (x y z)
          (run-2-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z))) 

*2-step-run-ex*


(defconst *3-step-run-ex*
  (mv-let (x y z)
          (run-3-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z)))

*3-step-run-ex*


(defconst *4-step-run-ex*
  (mv-let (x y z)
          (run-4-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z)))

*4-step-run-ex*


(defconst *5-step-run-ex* 
  (mv-let (x y z)
          (run-5-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z)))

*5-step-run-ex*


(thm
 (mv-let (network-s initiator-s responder-s)
         *5-step-run-ex*
         (declare (ignore network-s))

         (and
          ;; responder stores the correct partner
          (equal (id *initiator-constants*)
                 (id-i responder-s))

          ;; Initiator stores the correct partner
          (equal (id *responder-constants*)
                 (id-r initiator-s))
              
          (equal (session-key initiator-s)
                 (session-key responder-s))))))
