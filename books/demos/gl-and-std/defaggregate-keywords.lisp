; Integration of STD and FTY with GL Demos
; Copyright (C) 2015, Oracle and/or its affiliates. All rights reserved.
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
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

(include-book "std/top" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/gl/def-gl-rule" :dir :system)

(def-gl-clause-processor my-glcp)

(std::defenum player-count-p
              (:zero :one :two :three))

(defconst *baseball* 0)
(defconst *basketball* 1)
(defconst *soccerball* 2)
(defconst *volleyball* 3)

(make-event
 `(std::defenum ball-p
                (,*baseball* ,*basketball* ,*soccerball* ,*volleyball*)))

(std::defaggregate sport
  ((player-count player-count-p
                 "Number of players, denoted with symbols instead of integers.")
   (ball ball-p))
  :layout :list)

(define set-sport-to-basketball
  ((sport sport-p))
  (change-sport sport :ball *basketball*))

(defrule basketball-p-of-set-sport-to-basketball
  (implies (sport-p sport)
           (equal (sport->ball (set-sport-to-basketball sport))
                  *basketball*))
  :enable (set-sport-to-basketball))

(def-gl-rule basketball-p-of-set-sport-to-basketball-via-gl
  :hyp (sport-p sport)
  :concl (equal (sport->ball (set-sport-to-basketball sport))
                *basketball*)
  :g-bindings `((sport ((player-count . ,(gl::g-ite '(:g-boolean . 0)
                                                    :zero
                                                    (gl::g-ite '(:g-boolean . 1)
                                                               :one
                                                               (gl::g-ite '(:g-boolean . 2)
                                                               :two
                                                               :three))))
                        (ball . (:g-number (3 4 5)))))))
