; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "terms-2")
(%interactive)


(%autoadmit logic.functionp)
(%autoadmit logic.function)
(%autoadmit logic.function-name)
(%autoadmit logic.function-args)

(%noexec logic.function)

(%autoprove booleanp-of-logic.functionp
            (%enable default logic.functionp))

(%autoprove consp-when-logic.functionp-cheap
            (%enable default logic.functionp))

(%autoprove logic.variablep-when-logic.functionp
            (%enable default logic.functionp))

(%autoprove logic.constantp-when-logic.functionp
            (%enable default logic.functionp))

(%autoprove consp-of-logic.function
            (%enable default logic.function))

(%autoprove logic.function-under-iff
            (%enable default logic.function))

(%autoprove forcing-logic.constantp-of-logic.function
            (%enable default logic.function))

(%autoprove forcing-logic.variablep-of-logic.function
            (%enable default logic.function))

(%autoprove forcing-logic.termp-of-logic.function
            (%enable default logic.function)
            (%restrict default definition-of-logic.termp (equal x '(cons name args)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.functionp-of-logic.function
            (%enable default logic.functionp logic.function))

(%autoprove forcing-logic.function-namep-of-logic.function-name
            (%enable default logic.functionp logic.function-name))

(%autoprove logic.function-name-of-logic.function
            (%enable default logic.function-name logic.function))

(%autoprove forcing-true-listp-of-logic.function-args
            (%enable default logic.functionp logic.function-args)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.term-listp-of-logic.function-args
            (%enable default logic.functionp logic.function-args)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.function-args-of-logic.function
            (%enable default logic.function-args logic.function))

(%autoprove forcing-logic.function-of-logic.function-name-and-logic.function-args
            (%enable default logic.functionp logic.function logic.function-name logic.function-args))

(%autoprove logic.function-of-logic.function-name-and-nil-when-nil-logic.function-args
            (%enable default logic.functionp logic.function-name logic.function logic.function-args))

(%autoprove forcing-logic.function-of-logic.function-name-and-logic.function-args-free)

(%autoprove rank-of-logic.function-args
            (%enable default logic.function-args))

(%autoprove rank-of-first-of-logic.function-args
            (%enable default logic.function-args))

(%autoprove rank-of-second-of-logic.function-args
            (%enable default logic.function-args))

(%autoprove rank-of-third-of-logic.function-args
            (%enable default logic.function-args))

(%autoprove equal-of-logic.function-rewrite
            (%enable default logic.function logic.functionp logic.function-name logic.function-args))


(defthm equal-of-logic.function-rewrite-alt
  ;; bozo add this to acl2
  (implies (force (logic.function-namep name))
           (equal (equal x (logic.function name args))
                  (and (logic.functionp x)
                       (equal (logic.function-name x) name)
                       (equal (logic.function-args x) args))))
  :hints(("goal" :use ((:instance equal-of-logic.function-rewrite)))))

(%autoprove equal-of-logic.function-rewrite-alt
            (%use (%instance (%thm equal-of-logic.function-rewrite))))

(%autoprove equal-of-logic.function-and-logic.function
            (%enable default logic.function))

(%autoprove logic.function-args-under-iff-with-len-free)



(%autoprove forcing-equal-of-logic.function-with-two-args)

(defthm forcing-equal-of-logic.function-with-two-args-alt
  (implies (and (equal (len (logic.function-args x)) 2)
                (force (logic.termp x))
                (force (logic.functionp x)))
           (equal (equal x (logic.function name (list a b)))
                  (and (equal name (logic.function-name x))
                       (equal a (first (logic.function-args x)))
                       (equal b (second (logic.function-args x)))))))

(%autoprove forcing-equal-of-logic.function-with-two-args-alt
            (%use (%thm forcing-equal-of-logic.function-with-two-args)))




(%autoprove forcing-equal-of-logic.function-with-three-args)

(defthm forcing-equal-of-logic.function-with-three-args-alt
               (implies (and (equal 3 (len (logic.function-args x)))
                             (force (logic.termp x))
                             (force (logic.functionp x)))
                        (equal (equal x (logic.function name (list a b c)))
                               (and (equal name (logic.function-name x))
                                    (equal a (first (logic.function-args x)))
                                    (equal b (second (logic.function-args x)))
                                    (equal c (third (logic.function-args x)))))))

(%autoprove forcing-equal-of-logic.function-with-three-args-alt
            (%use (%instance (%thm forcing-equal-of-logic.function-with-three-args))))

