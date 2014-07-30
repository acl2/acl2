; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2013 Centaur Technology
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

; sfaig.lisp
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "sexpr-to-faig")
(include-book "sexpr-vars-1pass")
(include-book "g-sexpr-eval") ;; BOZO for varmap stuff, split this out
(local (include-book "std/util/defprojection" :dir :system))

(local (in-theory (disable*  4v-sexpr-eval
                             4v-sexpr-alist-extract
                             4v-lookup
                             4v-sexpr-apply
                             faig-eval
                             num-varmap
                             4v-sexpr-to-faig
                             4v-sexpr-to-faig-plain
                             faig-const->4v
                             4v->faig-const
                             sig-al-to-svar-al
                             4v-alist->faig-const-alist)))

(local
 (defthm alist-keys-of-4v-sexpr-alist-extract
   ;; BOZO find me a home
   (equal (alist-keys (4v-sexpr-alist-extract keys env))
          (list-fix keys))
   :hints(("Goal" :in-theory (enable 4v-sexpr-alist-extract)))))

(local
 (defsection sexpr-env-reduce

   ;; Technical lemma.  This basically shows that we don't need to consider any
   ;; variables that are bound in an environment that aren't used in the sexpr.

   (local (defthm lemma
            (implies (member x vars)
                     (equal (4v-lookup x (4v-sexpr-alist-extract vars env))
                            (4v-lookup x env)))
            :hints(("Goal" :in-theory (enable 4v-sexpr-alist-extract
                                              4v-lookup)))))

   (defthm-4v-sexpr-flag
     ;; BOZO find me a home
     (defthm 4v-sexpr-eval-of-4v-sexpr-alist-extract-all-vars
       (implies (subsetp (4v-sexpr-vars x) vars)
                (equal (4v-sexpr-eval x (4v-sexpr-alist-extract vars env))
                       (4v-sexpr-eval x env)))
       :flag sexpr)
     (defthm 4v-sexpr-eval-list-of-4v-sexpr-alist-extract-all-vars
       (implies (subsetp (4v-sexpr-vars-list x) vars)
                (equal (4v-sexpr-eval-list x (4v-sexpr-alist-extract vars env))
                       (4v-sexpr-eval-list x env)))
       :flag sexpr-list)
     :hints(("Goal"
             :in-theory (enable 4v-sexpr-eval 4v-sexpr-eval-list))))))

(define sfaig
  :parents (4v-sexprs 4v-sexpr-to-faig)
  :short "A simplified version of @(see 4v-sexpr-to-faig) that constructs its
own onoff list out of the variables of the sexpr."

  ((sexpr "A single 4v-sexpr."))
  :returns (faig "An equivalent FAIG, using numeric variables.")

  (b* ((vars  (4v-sexpr-vars-1pass sexpr))
       (onoff (num-varmap vars 0)))
    (4v-sexpr-to-faig sexpr onoff)))

(define sfaig-make-faigenv
  :parents (sfaig)
  :short "For use with @(see sfaig), translates sexpr
environments into equivalent faig environments."

  ((sexpr "A single 4v-sexpr.")
   (env   "A sexpr-env to evaluate it under."))
  :returns
  (faig-env "The corresponding faig environment.")

  (b* ((vars  (4v-sexpr-vars-1pass sexpr))
       (onoff (num-varmap vars 0))
       (env
        ;; Technical stupidity that we probably don't really need; this is just
        ;; here to make 4v-alist-equiv-faig-const-alist->4v-alist-lemma fit well
        ;; with this definition.
        (4v-sexpr-alist-extract vars env)))
    (sig-al-to-svar-al (4v-alist->faig-const-alist env) onoff))

  ///
  (local (in-theory (enable sfaig)))

  (defthm faig-eval-of-sfaig-make-faigenv
    (b* ((faig     (sfaig sexpr))
         (faig-env (sfaig-make-faigenv sexpr env)))
      (equal (faig-eval faig faig-env)
             (4v->faig-const (4v-sexpr-eval sexpr env))))
    :hints(("Goal"
            :in-theory (disable 4v-alist-equiv-faig-const-alist->4v-alist-lemma)
            :use ((:instance 4v-alist-equiv-faig-const-alist->4v-alist-lemma
                             (al (4v-sexpr-alist-extract (4v-sexpr-vars sexpr)
                                                         env))))))))

(define sfaig-recover-4venv
  :parents (sfaig)
  :short "For use with @(see sfaig), translates faig environments into
equivalent sexpr environments."
  ((sexpr    "A single 4v-sexpr.")
   (faig-env "A faig-env to evaluate the corresponding faig."))
  :returns
  (sexpr-env "The corresponding sexpr environment.")

  (b* ((vars  (4v-sexpr-vars-1pass sexpr))
       (onoff (num-varmap vars 0)))
    (faig-const-alist->4v-alist
     (faig-eval-alist onoff faig-env)))

  ///
  (local (in-theory (enable sfaig)))

  (defthm sexpr-eval-of-sfaig-recover-4venv
    (b* ((faig      (sfaig sexpr))
         (sexpr-env (sfaig-recover-4venv sexpr faig-env)))
      (equal (4v-sexpr-eval sexpr sexpr-env)
             (faig-const->4v (faig-eval faig faig-env))))))




(define sfaiglist
  :parents (sfaig 4v-sexpr-to-faig-list)
  :short "A simplified version of @(see 4v-sexpr-to-faig-list) that constructs
its own onoff list out of the variables of the sexprs."

  ((sexprs "A list of @(see 4v-sexprs)."))
  :returns (faigs "A list of equivalent FAIGs, using numeric variables.")

  (b* ((vars  (4v-sexpr-vars-1pass-list sexprs))
       (onoff (num-varmap vars 0)))
    (4v-sexpr-to-faig-list sexprs onoff))

  ///
  (defthm len-of-sfaiglist
    (equal (len (sfaiglist x))
           (len x))))

(define sfaiglist-make-faigenv
  :parents (sfaig)
  :short "For use with @(see sfaiglist), translates sexpr environments into
equivalent faig environments."

  ((sexprs "The list of @(see 4v-sexprs).")
   (env    "A sexpr-env to evaluate them under."))
  :returns
  (faig-env "The corresponding faig environment.")

  (b* ((vars  (4v-sexpr-vars-1pass-list sexprs))
       (onoff (num-varmap vars 0))
       (env
        ;; Technical stupidity that we probably don't really need; this is just
        ;; here to make 4v-alist-equiv-faig-const-alist->4v-alist-lemma fit well
        ;; with this definition.
        (4v-sexpr-alist-extract vars env)))
    (sig-al-to-svar-al (4v-alist->faig-const-alist env) onoff))

  ///
  (local (in-theory (enable sfaiglist)))
  (defthm faig-eval-list-of-sfaiglist-make-faigenv
    (b* ((faigs    (sfaiglist sexprs))
         (faig-env (sfaiglist-make-faigenv sexprs env)))
      (equal (faig-eval-list faigs faig-env)
             (4v-list->faig-const-list (4v-sexpr-eval-list sexprs env))))
    :hints(("Goal"
            :in-theory (disable 4v-alist-equiv-faig-const-alist->4v-alist-lemma)
            :use ((:instance 4v-alist-equiv-faig-const-alist->4v-alist-lemma
                             (al (4v-sexpr-alist-extract
                                  (4v-sexpr-vars-list sexprs)
                                  env))))))))

(define sfaiglist-recover-4venv
  :parents (sfaig)
  :short "For use with @(see sfaiglist), translates faig environments back into
equivalent sexpr environments."
  ((sexprs   "The list of @(see 4v-sexprs).")
   (faig-env "A faig-env to evaluate the corresponding faigs."))
  :returns
  (sexpr-env "The corresponding sexpr environment.")

  (b* ((vars  (4v-sexpr-vars-1pass-list sexprs))
       (onoff (num-varmap vars 0)))
    (faig-const-alist->4v-alist
     (faig-eval-alist onoff faig-env)))

  ///
  (local (in-theory (enable sfaiglist)))

  (local (std::defprojection 4v-list-fix (x)
           (4v-fix x)
           :optimize nil))

  (local (defthm faig-const-list->4v-list-of-4v-list->faig-const-list
           (equal (faig-const-list->4v-list
                   (4v-list->faig-const-list x))
                  (4v-list-fix x))
           :hints(("Goal" :in-theory (enable faig-const-list->4v-list
                                             4v-list->faig-const-list)))))

  (local (defthm 4v-list-fix-of-4v-sexpr-eval-list
           (equal (4v-list-fix (4v-sexpr-eval-list sexprs env))
                  (4v-sexpr-eval-list sexprs env))
           :hints(("Goal" :induct (len sexprs)))))

  (defthm 4v-sexpr-eval-list-of-sfaiglist-recover-4venv
    (b* ((faigs     (sfaiglist sexprs))
         (sexpr-env (sfaiglist-recover-4venv sexprs faig-env)))
      (equal (4v-sexpr-eval-list sexprs sexpr-env)
             (faig-const-list->4v-list
              (faig-eval-list faigs faig-env))))))

