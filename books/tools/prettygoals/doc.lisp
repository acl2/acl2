; Pretty Goals for ACL2
; Copyright (C) 2016 Kookamara LLC
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

(in-package "PRETTYGOALS")
(include-book "xdoc/top" :dir :system)

(defsection prettygoals
  :short "Experimental tool for displaying proof goals in a prettier way."

  :long "<p>This tool changes how ACL2 prints proof goals to be ``prettier,''
 so that you can more quickly read them and understand why ACL2 is stuck.</p>

 <p>Note: this is experimental and may change drastically in the future.  It is
 also an unprincipled tool that may screw up your goals.  Please use it with
 caution.  Send any feedback on it to Jared Davis.</p>


 <h3>Usage</h3>

 <p>Either manually or via your @(see acl2::acl2-customization) file, do:</p>

 @({
      (include-book \"tools/prettygoals/top\" :dir :system)
 })

 <p>Subsequent proof goals will now be made prettier.  You can also turn
 this on an off:</p>

 @({
      (include-book \"tools/prettygoals/top\" :dir :system)

      (defthm foo ...)          ;; proof goals will be pretty

      (set-pretty-goals nil)
      (defthm bar ...)          ;; proof goals will be ugly

      (set-pretty-goals t)
      (defthm baz ...)          ;; proof goals will be pretty
 })


 <h3>Effects</h3>

 <h4>Readable B* Binders for Structure Accessors</h4>

 <p>Background: macros like @(see std::defaggregate) and @(see fty::defprod)
 introduce fancy @(see b*) binders that let you refer to accessors using a
 concise, dot-style notation like @('mystudent.name') in place of the more
 verbose @('(student->name mystudent)').</p>

 <p>ACL2's ``untranslate'' mechanisms don't know about or preserve this
 syntax, so when you give it a goal like this:</p>

 @({
      (defthm xx
        (b* (((student x))
             ((airplane y)))
          (concl (list x.name x.age x.major y.wings y.wheels))))
 })

 <p>It prints out all the accessors in full, like this:</p>

 @({
      *** Key checkpoint at the top level: ***

      Goal''
      (CONCL (LIST (STUDENT->NAME X)
                   (STUDENT->AGE X)
                   (STUDENT->MAJOR X)
                   (AIRPLANE->WINGS Y)
                   (AIRPLANE->WHEELS Y)))
 })

 <p>Prettygoals reintroduces the @(see b*) binders so you instead see:</p>

 @({
      *** Key checkpoint at the top level: ***

      (B* (((STUDENT X)) ((AIRPLANE Y)))
          (CONCL (LIST X.NAME X.AGE X.MAJOR Y.WINGS Y.WHEELS)))
 })


 <h4>Type Error Warnings</h4>

 <p>Occasionally you may submit a theorem with a typo, for instance, notice how
 we are accessing both @('(student->... x)') and @('(airplane->... x)') in the
 following goal:</p>

 @({
      (defthm yy
        (concl (list (student->name x)
                     (student->age x)
                     (airplane->wings x)
                     (airplane->wheels y))))
 })

 <p>When pretty goals are enabled and you try to access the same structure in
 different ways, we may be able to notice and add a warning, e.g.,:</p>

 @({
      *** Key checkpoint at the top level: ***

      Goal
      (B* (((STUDENT X))
           ((AIRPLANE X))
           ((AIRPLANE Y)))
          \"WARNING: type confusion: ((X STUDENT X) (X AIRPLANE X))\"
          (CONCL (LIST X.NAME X.AGE X.WINGS Y.WHEELS))) 
 })


 <h4>Simpler Hyps First</h4>



 <h4>Original Motivation</h4>

 <p>I was working on a proof when I encountered the following subgoal:</p>

 @({
      (IMPLIES (AND (SIGNED-BYTE-P (BIGBOUND->SIZE BOUND1)
                                   (BIGINT->VAL (BIGEVAL ARG1 ENV)))
                    (NOT (BIGBOUND->MIN BOUND1))
                    (<= (BIGINT->VAL (BIGEVAL ARG1 ENV))
                        (BIGBOUND->MAX BOUND1))
                    (SIGNED-BYTE-P (BIGBOUND->SIZE BOUND2)
                                   (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                    (<= (BIGBOUND->MIN BOUND2)
                        (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                    (NOT (BIGBOUND->MAX BOUND2))
                    (BIGBOUND->MAX BOUND1)
                    (< 0 (BIGBOUND->MAX BOUND1))
                    (BIGBOUND->MIN BOUND2)
                    (<= 0 (BIGBOUND->MIN BOUND2))
                    (<= (+ 1 (BIGBOUND->MAX BOUND1))
                        (BIGBOUND->SIZE BOUND2)))
               (<= (LOGHEAD (BIGINT->VAL (BIGEVAL ARG1 ENV))
                            (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                   (+ -1 (ASH 1 (BIGBOUND->SIZE BOUND1)))))
 })

 <p>This goal is really messy and annoying.  I at least wanted ACL2 to replace
 things like @('(bigbound->min bound1)') with @('bound1.min').  After doing
 that, the goal was still a mess because simple things like @('bound1.max')
 were jammed between complicated goals, which suggested reordering the
 hypotheses based on how complex they are.  The above goal now prints instead
 as follows, which I think is a lot more pleasant.</p>

 @({
      (B* (((BIGBOUND BOUND1))
           ((BIGBOUND BOUND2)))
        (IMPLIES (AND BOUND1.MAX BOUND2.MIN (NOT BOUND1.MIN)
                      (NOT BOUND2.MAX)
                      (< 0 BOUND1.MAX)
                      (<= 0 BOUND2.MIN)
                      (<= (+ 1 BOUND1.MAX) BOUND2.SIZE)
                      (<= BOUND2.MIN
                          (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                      (<= (BIGINT->VAL (BIGEVAL ARG1 ENV))
                          BOUND1.MAX)
                      (SIGNED-BYTE-P BOUND1.SIZE
                                     (BIGINT->VAL (BIGEVAL ARG1 ENV)))
                      (SIGNED-BYTE-P BOUND2.SIZE
                                     (BIGINT->VAL (BIGEVAL ARG2 ENV))))
                 (<= (LOGHEAD (BIGINT->VAL (BIGEVAL ARG1 ENV))
                              (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                     (+ -1 (ASH 1 BOUND1.SIZE)))))
 })

 <p>There are probably a lot of other ways to improve this.  For instance it
 might be nice to put hyps about related variables close together, or otherwise
 try to group up the hyps into a sensible order.  We could also look for
 potential typos in variable names, and so on...</p>")
