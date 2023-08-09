; Multiplier verification

; Copyright (C) 2023 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)

(include-book "heuristics")
(include-book "adder-patterns")
(include-book "quick-search")
(include-book "macros")

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (defthm svexlist-p-of-remove-duplicates
   (implies (sv::Svexlist-p x)
            (sv::Svexlist-p (remove-duplicates-equal x)))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(local
 (in-theory (e/d (acl2::maybe-integerp
                  sv::svex-kind)
                 ((:e tau-system)))))

(local
 (defthm sv::svexlist-eval$-when-consp
   (implies (consp lst)
            (equal (sv::svexlist-eval$ lst env)
                   (cons (sv::svex-eval$ (car lst) env)
                         (sv::svexlist-eval$ (cdr lst) env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Careful search after initial replacements to see if any patterns are missed.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection process-fa/ha-c-chain-pattern-args
  ;; Goal here is  to take a pattern-alist, and create  another fast-alist that
  ;; can be  used to find missed  fa-s/ha-s patterns. If  one of the args  of a
  ;; found fa-c/ha-c is  a bitxor, these function also  "explode" that argument
  ;; for a  more comprehensive  search.  Since  xor chains  can be  large, this
  ;; explosion     is    done     with     a    depth     limit    given     in
  ;; *process-fa/ha-c-chain-pattern-args-limit*.

  ;; For example, assume we have: (fa-c-chain  x y (bitxor m n)). And somewhere
  ;; else  in  the svex,  we  have  (bitxor m  (bitxor  x  (bitxor n  y))).   A
  ;; corresponding full-adder  sum pattern can  be pulled out from  this bitxor
  ;; chain.   So we  take this  already found  fa-c-chain pattern,  explode its
  ;; bitxor arguments and create a possible  search clue list containing: x y m
  ;; n. If we can  find an bitxor chain containing all  these values, then that
  ;; bitxor chain can be marked as a counterpart full-adder sum pattern.

  ;; The same thing  applies for when looking for half-adder  sum patterns from
  ;; half-adder carry.

  ;; These functions are not only useful for when looking for sum patterns from
  ;; already  found carry.  But  they  are also  useful  for  when looking  for
  ;; half-adder carry patterns from already found half-adder sum patterns.

  ;; TODO: expand this for ha+1 cases.

  ;; first define aux data types for easy programming.
  (fty::defprod exploded-args-and-args
    ((exploded-args sv::Svexlist-p) ;; exploded args
     (args sv::Svexlist-p) ;; original args as appears in full-adder carry chain.
     (column acl2::maybe-integerp))
    :layout :fulltree
    ;;:hons t
    )

  (fty::deflist exploded-args-and-args-list
                :elt-type exploded-args-and-args
                :true-listp t)

  (fty::defalist exploded-args-and-args-alist
                 :key-type sv::svex-p
                 :val-type exploded-args-and-args-list
                 :true-listp nil)

  (local
   (in-theory (disable ACL2::TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX
                       REMOVE-DUPLICATES-EQUAL
                       TRUE-LIST-LISTP
                       MEMBER-EQUAL)))

  (defthm exploded-args-and-args-alist-and-hons-assoc
    (implies (and (exploded-args-and-args-alist-p alist)
                  (hons-assoc-equal key alist))
             (and (sv::svex-p (car (hons-assoc-equal key alist)))
                  (exploded-args-and-args-list-p (cdr (hons-assoc-equal key alist)))))
    :hints (("Goal"
             :in-theory (e/d (exploded-args-and-args-alist-p) ()))))

  ;; define  an invariant  as need  to  know at  all times  that exploded  args
  ;; correspond to original args.
  (define exploded-args-and-args-inv ((x exploded-args-and-args-p)
                                      env
                                      &key
                                      ((bit-fn symbolp) 'bit-fn))
    :verify-guards nil
    (b* (((exploded-args-and-args x) x))
      (cond ((equal bit-fn 'sv::bitand) ;; when looking for ha-c from ha-s
             (equal (svl::svex-eval$-bitand-lst x.exploded-args env)
                    (svl::svex-eval$-bitand-lst x.args env)))
            ((equal bit-fn 'sv::bitor) ;; when looking for ha-c from ha-s
             (equal (svl::svex-eval$-bitor-lst x.exploded-args env)
                    (svl::svex-eval$-bitor-lst x.args env)))
            (t
             ;; otherwise expect to find bitxor at all times.
             (equal (svl::svex-eval$-bitxor-lst x.exploded-args env)
                    (svl::svex-eval$-bitxor-lst x.args env))))))

  (define exploded-args-and-args-list-inv ((lst exploded-args-and-args-list-p)
                                           env
                                           &key
                                           ((bit-fn symbolp) 'bit-fn))
    :verify-guards nil
    (if (atom lst)
        (equal lst nil)
      (and (exploded-args-and-args-inv (car lst) env)
           (exploded-args-and-args-list-inv (cdr lst) env))))

  (define exploded-args-and-args-alist-inv ((alist exploded-args-and-args-alist-p)
                                            env
                                            &key
                                            ((bit-fn symbolp) 'bit-fn))
    :verify-guards nil
    (if (atom alist)
        (symbolp alist)
      (and (exploded-args-and-args-list-inv (cdar alist) env)
           (exploded-args-and-args-alist-inv (cdr alist) env)))
    ///

    (defthm exploded-args-and-args-alist-inv-x-is-symbol
      (implies (symbolp x)
               (exploded-args-and-args-alist-inv x env))
      :rule-classes :type-prescription)

    (defthm exploded-args-and-args-alist-inv-x-is-nil
      (exploded-args-and-args-alist-inv nil env))

    (defthm exploded-args-and-args-alist-inv-hons-assoc
      (implies (exploded-args-and-args-alist-inv alist env)
               (exploded-args-and-args-list-inv (cdr (hons-assoc-equal key alist)) env))
      :hints (("Goal"
               :expand (EXPLODED-ARGS-AND-ARGS-LIST-INV NIL ENV)
               :in-theory (e/d () ())))))

  ;; set a limit for explosion in order to save time.
  (define process-fa/ha-c-chain-pattern-args-limit ()
    :returns (res natp)
    (if (aggressive-find-adders-in-svex) ;; agressive search will trigger a deeper explosion.
        5
      2) ; 2 should be sufficient for the majority of cases if not all.
    ///
    (in-theory (disable (:e process-fa/ha-c-chain-pattern-args-limit))))

  ;; Need to create a fast-alist to lookup possibly matching arguments quickly.
  ;; This function pick a  the best key. It looks like it is  best for this key
  ;; to not be  a partsel of a variable  OR when an argument is  a constant.  I
  ;; cannot recall  why this  is the  case and  this may  now be  redundant. It
  ;; probably helps with speed ups. Note that it may still select these as keys
  ;; if no other leaf is left.
  (define cons-with-best-first-key (leaves rest-keys)
    ;; chosing constants or simple partsel of input operands is not a good choice usually...
    :returns (keys sv::svexlist-p :hyp (and (sv::Svexlist-p leaves)
                                            (sv::Svexlist-p rest-keys)))
    (if (atom leaves)
        rest-keys
      (b* ((l (car leaves))
           ((when (and (or (integerp l)
                           (case-match l
                             (('sv::partsel & & x)
                              (atom x))))
                       (consp (cdr leaves))))
            (cons-with-best-first-key (cdr leaves) rest-keys)))
        (cons l rest-keys))))

  ;; Pull exploded args, and also create keys for quick lookups.
  (define process-fa/ha-c-chain-pattern-args-aux ((args)
                                                  &key
                                                  ((bit-fn symbolp) 'bit-fn))
    :prepwork
    ((local
      (defret consp-of-<fn>
        (consp svl::leaves)
        :fn svl::bitand/or/xor-collect-leaves2
        :hints (("Goal"
                 :in-theory (e/d (svl::bitand/or/xor-collect-leaves2) ()))))))

    :returns (mv (keys sv::svexlist-p :hyp (and (sv::Svexlist-p args)
                                                (force (or (equal bit-fn 'sv::bitand)
                                                           (equal bit-fn 'sv::bitor)
                                                           (equal bit-fn 'sv::bitxor)))))
                 (exploded-args sv::svexlist-p :hyp (and (sv::Svexlist-p args)
                                                         (force
                                                          (or (equal bit-fn 'sv::bitand)
                                                              (equal bit-fn 'sv::bitor)
                                                              (equal bit-fn 'sv::bitxor))))))
    (if (atom args)
        (mv nil nil)
      (b* (((mv rest-keys exploded-args)
            (process-fa/ha-c-chain-pattern-args-aux (cdr args)))
           ((mv leaves &)
            (svl::bitand/or/xor-collect-leaves2 (car args)
                                                bit-fn
                                                (process-fa/ha-c-chain-pattern-args-limit))))
        (mv (cons-with-best-first-key leaves rest-keys)
            (append leaves exploded-args))))
    ///
    (defret <fn>-is-correct
      (and (implies (equal bit-fn 'sv::bitxor)
                    (equal (svl::svex-eval$-bitxor-lst exploded-args env)
                           (svl::svex-eval$-bitxor-lst args env)))
           (implies (equal bit-fn 'sv::bitand)
                    (equal (svl::svex-eval$-bitand-lst exploded-args env)
                           (svl::svex-eval$-bitand-lst args env)))
           (implies (equal bit-fn 'sv::bitor)
                    (equal (svl::svex-eval$-bitor-lst exploded-args env)
                           (svl::svex-eval$-bitor-lst args env)))
           )
      :fn process-fa/ha-c-chain-pattern-args-aux))

  ;; create fast-alist  entries to  find exploded-args and  args. Note  that it
  ;; does not override already existing entries!!
  (define process-fa/ha-c-chain-pattern-args-collect-aux ((keys true-listp)
                                                          exploded-args-and-args
                                                          collected
                                                          &key
                                                          (enabled 't))
    :returns (collected-res exploded-args-and-args-alist-p
                            :hyp (and (exploded-args-and-args-alist-p collected)
                                      (or (not enabled) (sv::svexlist-p keys))
                                      (or (not enabled) (exploded-args-and-args-p exploded-args-and-args))))
    (if (atom keys)
        collected
      (b* (((unless enabled) collected)
           (key (car keys))
           (existing-entry (cdr (hons-get key collected)))
           (new-entry (cons exploded-args-and-args existing-entry)))
        (process-fa/ha-c-chain-pattern-args-collect-aux (cdr keys)
                                                        exploded-args-and-args
                                                        (hons-acons key new-entry collected)
                                                        :enabled enabled)))
    ///

    (defret <fn>-is-correct
      (implies (and (exploded-args-and-args-alist-inv collected env)
                    (or (not enabled)
                        (exploded-args-and-args-inv exploded-args-and-args env)))
               (exploded-args-and-args-alist-inv collected-res env))
      :hints (("Goal"
               :in-theory (e/d (exploded-args-and-args-alist-inv
                                exploded-args-and-args-list-inv)
                               ())))))

  (defthm svexlist-p-implies-true-listp
    (implies (sv::Svexlist-p x)
             (true-listp x))
    :rule-classes (:rewrite))

  ;; check inersection without consing.
  (define has-common-elements-p (l1 (l2 true-listp))
    (if (atom l1)
        nil
      (or (member-equal (car l1) l2)
          (has-common-elements-p (cdr l1) l2))))

  (local
   (in-theory (disable subsetp-equal)))

  (define safe-take ((num natp) x)
    :returns (res sv::svexlist-p :hyp (sv::svexlist-p x))
    (if (or (atom x)
            (zp num))
        nil
      (cons (car x)
            (safe-take (1- num) (cdr x)))))

  #|(local
  (defthm EXPLODED-ARGS-AND-ARGS-ALIST-P-implies-true-listp ;
  (implies (EXPLODED-ARGS-AND-ARGS-ALIST-P x) ;
  (true-listp x))))|#

  (local
   (defthmd dumb-true-listp-lemma
     (implies (true-listp x)
              (iff (consp x)
                   x))
     ))

  ;; (define pull-first-args-from-pattern-alist ((pattern-alist pattern-alist-p)
  ;;                                             (track-column?))
  ;;   :inline t
  ;;   :guard (consp pattern-alist)
  ;;   :returns (args sv::svexlist-p :hyp (and ;;(pattern-alist-p pattern-alist)
  ;;                                       (consp pattern-alist)))
  ;;   (b* ((args (caar (pattern-alist-fix pattern-alist)))
  ;;        (args (if  track-column? (cdr  args)  args)))
  ;;     ;;if track-column? is
  ;;     ;; activated,   then   the
  ;;     ;; first   arg   will   be
  ;;     ;; column number,  we need
  ;;     ;; to get rid of it.
  ;;     args))

  (define check-member-in-pattern-fns ((fn symbolp) fns
                                       &key
                                       (track-column? 'track-column?))
    (if (atom fns)
        nil
      (or (cond (track-column? ;; when track-column?,  a fn will be expected to
                 ;; be in the  form of (ha-c-chain .  5) where  5 is the column
                 ;; number that the match  should happen.  This function should
                 ;; return that number when
                 (and (consp (car fns))
                      (eq fn (caar fns))
                      (cdar fns)))
                (t (eq fn (car fns))))
          (check-member-in-pattern-fns fn (cdr fns)))))

  (with-output
    :off :all
    :on (error summary)
    :gag-mode nil
    (define process-fa/ha-c-chain-pattern-args ((pattern-alist pattern-alist-p)
                                                (collected exploded-args-and-args-alist-p)
                                                &key
                                                ((adder-type symbolp) 'adder-type)
                                                (track-column? 'track-column?))
      :returns (collected-res exploded-args-and-args-alist-p
                              :hyp (and (exploded-args-and-args-alist-p collected)
                                        (pattern-alist-p pattern-alist)))
      :guard-hints (("Goal")
                    (and stable-under-simplificationp
                         '(:in-theory (e/d (dumb-true-listp-lemma) ()))))
      (if (atom pattern-alist)
          collected
        (b* ((fns (cdar (pattern-alist-fix pattern-alist)))

             ;; if already has a pattern of its self, then don't be too hard on
             ;; it and avoid-column-check.  Setting the  column value to nil in
             ;; exploded-args-and-args  should  later  make  the  program  skip
             ;; column check.

             ((mv bit-fn column/match-p do-not-explode avoid-column-check)
              (cond ((eq adder-type 'ha)
                     (mv 'sv::bitxor (or (check-member-in-pattern-fns 'ha-c-chain fns)
                                         (check-member-in-pattern-fns 'ha+1-c-chain fns))
                         nil
                         (and*-exec track-column?
                                    (or* (check-member-in-pattern-fns 'ha-s-chain-self fns)
                                         (check-member-in-pattern-fns 'ha+1-s-chain-self fns)))))
                    ((eq adder-type 'ha-c) ;; ha-c will also be searched carefully like sum outputs.
                     (mv 'sv::bitand
                         (check-member-in-pattern-fns 'ha-s-chain fns)
                         nil ;;(check-member-in-pattern-fns 'ha-c-chain fns) ;;
                         ;;if there is already a full pattern, then don't
                         ;;explode..
                         (and*-exec track-column?
                                    (check-member-in-pattern-fns 'ha-s-chain-self fns))
                         ))
                    ((eq adder-type 'ha+1-c) ;; probably not fully implemented.
                     (mv 'sv::bitor
                         (check-member-in-pattern-fns 'ha+1-s-chain fns)
                         nil ;;(check-member-in-pattern-fns 'ha+1-c-chain fns)
                         ;; if there is already a full pattern, then don't
                         ;; explode..
                         (and*-exec track-column?
                                    (check-member-in-pattern-fns 'ha+1-s-chain-self fns))
                         ))
                    (t (mv 'sv::bitxor
                           (check-member-in-pattern-fns 'fa-c-chain fns)
                           nil
                           (and*-exec track-column?
                                      (check-member-in-pattern-fns 'fa-s-chain-self fns))))))
             ;; making the check subsetp-equal to still hit partially found fa-s/ha-s pairs.
             ((unless column/match-p)
              (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected))
             (args (caar (pattern-alist-fix pattern-alist)))
             ((when (and*-exec (eq adder-type 'ha) (or* (member 0 args) (member 1 args))))
              ;; constants should not be in args, at least for ha. if they are, ignore them..
              (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected))
             ((mv keys exploded-args)
              (if do-not-explode
                  (mv args args)
                (process-fa/ha-c-chain-pattern-args-aux args)))

             (keys (safe-take 1 keys)) ;; minimize the number of keys to prevent cluttering the collected alist

             (exploded-args-orig exploded-args)
             ;; remove  duplicates to  maximize  changes  why remove  duplicates:
             ;; because  the matching  pattern might  have already  simplifed the
             ;; repeated elements.
             (exploded-args (cond ((equal bit-fn 'sv::bitxor)
                                   (svl::remove-pair-equal exploded-args)
                                   #|(remove-equal 0
                                   )|#)
                                  ((equal bit-fn 'sv::bitor)
                                   (remove-duplicates-equal exploded-args)
                                   #|(remove-equal 0
                                   )|#)
                                  ((equal bit-fn 'sv::bitand)
                                   (remove-duplicates-equal exploded-args))
                                  (t
                                   exploded-args ;; maybe make it remove duplicates or something.
                                   )))

             ;; All  viable  keys   could  have  been  removed   above  due  to
             ;; removing-pairs/duplicates above if that's the case, then extend
             ;; keys to make sure we can have a hit:
             (keys (if (implies (or keys ;;  keys might be intentionally empty if
                                    ;; so, then don't put  stuff in it unless the
                                    ;; agressive mode is enabled.
                                    (aggressive-find-adders-in-svex))
                                (has-common-elements-p keys exploded-args))
                       keys
                     (append (safe-take 1 exploded-args) keys)))

             (?exploded-args-and-args (make-exploded-args-and-args :exploded-args exploded-args
                                                                   :args args
                                                                   :column (and*-exec track-column?
                                                                                      (not* avoid-column-check)
                                                                                      (integerp column/match-p)
                                                                                      column/match-p)))
             (collected (process-fa/ha-c-chain-pattern-args-collect-aux keys exploded-args-and-args collected))

             (exploded-args-changed? (not (equal exploded-args-orig exploded-args)))
             (collected
              ;; do   this  below   when   removing  duplicates/pairs   changes
              ;; something. this makes  sure we have both  versions to increase
              ;; the chances.
              (process-fa/ha-c-chain-pattern-args-collect-aux keys
                                                              (and exploded-args-changed?
                                                                   (change-exploded-args-and-args
                                                                    exploded-args-and-args
                                                                    :exploded-args exploded-args-orig))
                                                              collected
                                                              :enabled exploded-args-changed?))

             )
          (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected)))
      ///

      (local
       (defthm atom-remove-pair-equal-lemma
         (implies (bind-free '((env . env)) (env))
                  (iff (consp (svl::remove-pair-equal lst))
                       (not (and (hide (not (consp (svl::remove-pair-equal lst))))
                                 (equal (svl::svex-eval$-bitxor-lst lst env)
                                        0)))))
         :hints (("goal"
                  :use ((:instance svl::svex-eval$-bitxor-lst-of-remove-pair-equal
                                   (svl::lst lst)))
                  :do-not-induct t
                  :expand ((:free (x) (hide x)))
                  :in-theory (e/d ()
                                  (svl::svex-eval$-bitxor-lst-of-remove-pair-equal
                                   svl::remove-pair-equal
                                   ;;svl::svex-eval$-bitxor-lst
                                   ))))))
      (defret <fn>-is-correct
        (and
         (implies (and (exploded-args-and-args-alist-inv collected env :bit-fn 'sv::bitand)
                       (equal adder-type 'ha-c))
                  (exploded-args-and-args-alist-inv collected-res env :bit-fn 'sv::bitand))
         (implies (and (exploded-args-and-args-alist-inv collected env :bit-fn 'sv::bitor)
                       (equal adder-type 'ha+1-c))
                  (exploded-args-and-args-alist-inv collected-res env :bit-fn 'sv::bitor))
         (implies (and (exploded-args-and-args-alist-inv collected env :bit-fn 'sv::bitxor)
                       (not (equal adder-type 'ha+1-c))
                       (not (equal adder-type 'ha-c)))
                  (exploded-args-and-args-alist-inv collected-res env :bit-fn 'sv::bitxor)))
        :hints (("Goal"
                 :do-not-induct t
                 :expand ((process-fa/ha-c-chain-pattern-args pattern-alist collected
                                                              :adder-type 'ha))
                 :induct (process-fa/ha-c-chain-pattern-args pattern-alist collected)
                 :in-theory (e/d (exploded-args-and-args
                                  exploded-args-and-args->exploded-args
                                  exploded-args-and-args->args
                                  exploded-args-and-args-inv)
                                 (if*
                                  pattern-alist-p-of-cons))))))))

(defsection careful-search-from-counterpart-svex-aux-explore
  ;; These functions perform  a "cheap" search to see if  all the exploded args
  ;; appear as an argument  in the bitxor (or bitand) chain of  an svex. AND it
  ;; makes sure  that exploded args  are distributed  into two branches  of the
  ;; topmost  bitxor/bitnad.  Why  topmost:  because we  want  to preserve  the
  ;; original structure  as much  as possible  and this  indicates that  we are
  ;; ready to  shuffle around  the svex to  reveal the  matching ha-s/fa-s/ha-c
  ;; pattern.

  ;; For example, assume we have already found this: (fa-c-chain x y z), and we
  ;; are looking for a counterpart fa-s in this term:

  ;; (bitxor (bitxor  x (bitxor  a (bitxor  y z))) (bitxor  k m)).   Since this
  ;; bitxor chain has x, y and z, we can say that this includes our counterpart
  ;; full-adder sum  pattern. One thing we  can do is shuffle  the arguments at
  ;; this stage to pull out the fa-s as follows:
  ;; (bitxor (fa-s-chain x y z) (bitxor a (bitxor k m)))
  ;; Another  option is  to dive  into  the first  branch of  the main  bitxor:
  ;; (bitxor  x (bitxor  a (bitxor  y z))),  and only  shuffle these  arguments
  ;; around. So we'd get:
  ;; (bitxor (bitxor a (fa-s-chain x y z)) (bitxor k m))
  ;; a logically  equivalent term but  syntactically different. I  preferred to
  ;; use the second  option because the first one causes  elements in bitxor to
  ;; be  moved  around  too  much  and it  changes  the  original  structure  a
  ;; lot. During development, this made it very difficult to debug things. So I
  ;; now dive in as much as possible before shuffling elements around to reveal
  ;; counterpart  full-adder sum  patterns.  It  is possible  that this  became
  ;; redundant now and that this may not have any benefits anymore but there is
  ;; no harm keeping  this system intact.  This may help  with debugging in the
  ;; feature.

  (local
   (defthm member-equal-of-hons-assoc-equal
     (implies (hons-assoc-equal x lst)
              (member-equal (hons-assoc-equal x lst)
                            lst))))
  (local
   (defthm sv::svexlist-p-implies-true-listp
     (implies (sv::svexlist-p lst)
              (true-listp lst))))

  ;; Find a possible match from exploded-args-and-args-alist.
  (define careful-search-from-counterpart-svex-aux-explore-aux ((svex)
                                                                (exploded-args-and-args-alist)
                                                                (skip true-listp)
                                                                &key
                                                                ((bit-fn symbolp) 'bit-fn))
    :returns (alist-entry (implies alist-entry
                                   (member-equal alist-entry exploded-args-and-args-alist)))
    (case-match svex
      ((fn x y)
       (and (equal bit-fn fn)
            (or  ;;  be  careful:  the  below ordering  in  (and  ...) is  very
             ;;  important. This makes  sure that the result  of hons-get is
             ;;  returned upon success. So do not swap!
             (and (not  (member-equal x skip))
                  (hons-get x exploded-args-and-args-alist))
             (and (not (member-equal y skip))
                  (hons-get y exploded-args-and-args-alist))
             (careful-search-from-counterpart-svex-aux-explore-aux x exploded-args-and-args-alist skip)
             (careful-search-from-counterpart-svex-aux-explore-aux y exploded-args-and-args-alist skip))))
      (& nil))
    ///
    (defret return-val-of-<fn>
      (implies (and alist-entry
                    (exploded-args-and-args-alist-p exploded-args-and-args-alist))
               (and (consp alist-entry)
                    (sv::svex-p (car alist-entry))
                    (exploded-args-and-args-list-p (cdr alist-entry))))
      :hints (("Goal"
               :in-theory (e/d () (true-listp hons-assoc-equal)))))

    (defret <fn>-is-correct
      (implies (and (exploded-args-and-args-alist-inv exploded-args-and-args-alist env)
                    alist-entry)
               (exploded-args-and-args-list-inv (cdr alist-entry) env))))

  (define find-s-from-found-c-guard (bit-fn svex)
    :inline t
    :enabled t
    (cond ((equal bit-fn 'sv::bitand)
           (bitand-pattern-p svex))
          ((equal bit-fn 'sv::bitor)
           (bitor-pattern-p svex))
          (t
           (bitxor-pattern-p svex))))

  ;; When this function returns 3, then it means the exploded-args appear in both
  ;; branches of the svex. It will indicate that rewriting the svex at this point
  ;; is a good idea.
  (define careful-search-from-counterpart-svex-aux-explore2 ((svex)
                                                             (exploded-args)
                                                             &key
                                                             ((bit-fn symbolp) 'bit-fn))
    :prepwork
    ((define careful-search-from-counterpart-svex-aux-arg-exists-p ((svex)
                                                                    (arg)
                                                                    &key
                                                                    ((bit-fn symbolp) 'bit-fn))
       :returns exists
       (or (hons-equal svex arg)
           (case-match svex
             ((fn x y)
              (and (equal fn bit-fn)
                   (or (careful-search-from-counterpart-svex-aux-arg-exists-p x arg)
                       (careful-search-from-counterpart-svex-aux-arg-exists-p y arg))))
             (& nil)))))
    :returns (exist-branch (and (acl2::maybe-integerp exist-branch)
                                (or (not exist-branch)
                                    (equal exist-branch 0)
                                    (equal exist-branch 1)
                                    (equal exist-branch 2)
                                    (equal exist-branch 3))))
    :guard (find-s-from-found-c-guard bit-fn svex)
    (if (atom exploded-args)
        0
      (b* ((rest (careful-search-from-counterpart-svex-aux-explore2 svex (cdr exploded-args)))
           ((Unless rest)
            nil)
           (cur (car exploded-args))
           (x (cadr svex))
           (exist-in-x (careful-search-from-counterpart-svex-aux-arg-exists-p x cur))
           ((when exist-in-x)
            (logior 1 rest))
           (y (caddr svex))
           (exist-in-y (careful-search-from-counterpart-svex-aux-arg-exists-p y cur))
           ((when exist-in-y)
            (logior 2 rest))
           ((when (integerp cur)) ;; will need to borrow a constant (likely 1 or -1).
            (logior 0 rest)))
        nil)))

  (define careful-search-from-counterpart-svex-aux-explore-list ((svex)
                                                                 (exploded-args-and-args-list exploded-args-and-args-list-p)
                                                                 &key
                                                                 ((bit-fn symbolp) 'bit-fn)
                                                                 ((column acl2::maybe-integerp) 'column)
                                                                 ;; give a large limit for measure. I don't expect this to go too big.
                                                                 )
    :guard-debug t
    :guard (find-s-from-found-c-guard bit-fn svex)
    :returns #|(mv (args sv::svexlist-p :hyp (force (exploded-args-and-args-list-p exploded-args-and-args-list)))
    (exploded-args sv::svexlist-p :hyp (force (exploded-args-and-args-list-p
    exploded-args-and-args-list)))
    (column acl2::maybe-integerp :hyp (force (exploded-args-and-args-list-p exploded-args-and-args-list)))
    )|#
    (exploded-args-and-args exploded-args-and-args-p :hyp (force (exploded-args-and-args-list-p exploded-args-and-args-list)))

    (if (atom exploded-args-and-args-list)
        (make-exploded-args-and-args) ;;(mv nil nil nil)
      (b* (((exploded-args-and-args cur) (car exploded-args-and-args-list))
           ((when (and*-exec column cur.column
                             ;; this is not  a great way to do  this because it
                             ;; will mess up column value when it is full-adder that is missed.
                             (not (equal cur.column (if* (eq bit-fn 'sv::bitxor) column (1- column))))))
            (careful-search-from-counterpart-svex-aux-explore-list svex (cdr exploded-args-and-args-list)))
           (args cur.args)
           (exploded-ags cur.exploded-args)
           ;; See if all the exploded-args  are present in svex. Also determine
           ;; if  they are  dispersed into  two branches  of bitxor  (bitand if
           ;; working for ha-c), or if they all  appear in only one of them. If
           ;; they  appear in  only  one of  the branches,  it  means the  same
           ;; pattern can be  applied down the line.  In order  to preserve the
           ;; SVEX'es structure  as much  as possible,  we avoid  applying such
           ;; matches when it is too early.
           (exist-branch (careful-search-from-counterpart-svex-aux-explore2 svex exploded-ags))
           ;; 3 means all exploded-args exist, and they are dispersed to the two branches.
           ((when (equal exist-branch 3))
            (progn$ (and*-exec
                     ;; a  check  to print a warning message  when  ha/ha-c is  being
                     ;; searched, it didn't just match the svex itself. Catching such a case
                     ;; might indicate something went wrong along the way because that would
                     ;; have been caught in quick search stage.
                     (svl::equal-len args 2)
                     (consp svex)
                     (subsetp-equal args (cdr svex))
                     (subsetp-equal (cdr svex) args)
                     (cwe "WARNING: Careful search found something that should have been matched in the quick search stage.~%"))
                    cur
                    #|(mv args exploded-ags cur.column)|#)))

        ;;if exist-branch is not 3, then keep searching for other matches.
        (careful-search-from-counterpart-svex-aux-explore-list svex (cdr exploded-args-and-args-list))))
    ///
    (defret <fn>-is-correct
      (b* (((exploded-args-and-args cur) exploded-args-and-args))
        (implies (and (exploded-args-and-args-list-inv exploded-args-and-args-list env)
                      cur.args)
                 (and (implies (equal bit-fn 'sv::bitxor)
                               (equal (svl::svex-eval$-bitxor-lst cur.args env)
                                      (svl::svex-eval$-bitxor-lst cur.exploded-args env)))
                      (implies (equal bit-fn 'sv::bitand)
                               (equal (svl::svex-eval$-bitand-lst cur.args env)
                                      (svl::svex-eval$-bitand-lst cur.exploded-args env)
                                      ))
                      (implies (equal bit-fn 'sv::bitor)
                               (equal (svl::svex-eval$-bitor-lst cur.args env)
                                      (svl::svex-eval$-bitor-lst cur.exploded-args env)
                                      )))))
      :hints (("Goal"
               :in-theory (e/d (exploded-args-and-args-list-inv
                                exploded-args-and-args-inv
                                )
                               ())))))

  ;; This function should return ARGS and EXPLODED-ARGS  that are ready to be applied the svex
  (define careful-search-from-counterpart-svex-aux-explore ((svex)
                                                            (exploded-args-and-args-alist exploded-args-and-args-alist-p)
                                                            (skip true-listp)
                                                            &key
                                                            ((bit-fn symbolp) 'bit-fn)
                                                            ((column acl2::maybe-integerp) 'column)
                                                            ;; give a large limit for measure. I don't expect this to go too big.
                                                            ((limit natp) '1000))
    :guard-debug t
    :guard (find-s-from-found-c-guard bit-fn svex)
    :returns (exploded-args-and-args exploded-args-and-args-p
                                     :hyp (force (exploded-args-and-args-alist-p exploded-args-and-args-alist)))
    #|(mv (args sv::svexlist-p :hyp (force (exploded-args-and-args-alist-p exploded-args-and-args-alist)))
    (exploded-args sv::svexlist-p :hyp (force (exploded-args-and-args-alist-p ;
    exploded-args-and-args-alist))))|#
    :measure (nfix limit)
    (if (zp limit)
        (make-exploded-args-and-args) ;;(mv nil nil)
      (b* (;; find  the first candidate by  looking up only one key.  It is not
           ;; guaranteed for other args to be present.
           (entry (careful-search-from-counterpart-svex-aux-explore-aux svex exploded-args-and-args-alist skip))
           ((Unless entry)
            (make-exploded-args-and-args)#|(Mv nil nil)|#)
           (key (car entry))
           (exploded-args-and-args-list (cdr entry))
           ((exploded-args-and-args cur)
            (careful-search-from-counterpart-svex-aux-explore-list svex exploded-args-and-args-list))
           ((when (and cur.args))
            cur))
        (careful-search-from-counterpart-svex-aux-explore svex exploded-args-and-args-alist
                                                          (cons key skip)
                                                          :limit (1- limit))))
    ///
    (defret <fn>-is-correct
      (b* (((exploded-args-and-args cur) exploded-args-and-args))
        (implies (and (exploded-args-and-args-alist-inv exploded-args-and-args-alist env)
                      cur.args)
                 (and (implies (equal bit-fn 'sv::bitxor)
                               (equal (svl::svex-eval$-bitxor-lst cur.args env)
                                      (svl::svex-eval$-bitxor-lst cur.exploded-args env)))
                      (implies (equal bit-fn 'sv::bitor)
                               (equal (svl::svex-eval$-bitor-lst cur.args env)
                                      (svl::svex-eval$-bitor-lst cur.exploded-args env)))
                      (implies (equal bit-fn 'sv::bitand)
                               (equal (svl::svex-eval$-bitand-lst cur.args env)
                                      (svl::svex-eval$-bitand-lst cur.exploded-args env)
                                      ))))))))

; Matt K. mod, 2/20/2023: The use of (logbitp-reasoning) makes ACL2(p) with
; waterfall-parallelism enabled complain that "the form (LOGBITP-REASONING) was
; expected to represent an ordinary value, not an error triple (mv erp val
; state), as would be acceptable in a serial execution of ACL2".  So I'll turn
; off waterfall parallelism here.
(local (set-waterfall-parallelism nil))

;; This is to remove everyting in to-remove-lst
;; When remaining-to-remove is nil, then it means everything in to-remove-lst was removed.
(define careful-search-from-counterpart-svex-aux-remove ((svex)
                                                         (to-remove-lst)
                                                         &key
                                                         ((bit-fn symbolp) 'bit-fn))

  :prepwork
  ((define remove-equal-once (x lst)
     :returns (res true-listp :hyp (true-listp lst))
     (cond ((atom lst)
            nil)
           ((equal x (car lst))
            (cdr lst))
           (t (cons-with-hint (car lst)
                              (remove-equal-once x (cdr lst))
                              lst)))
     ///
     (defret svexlist-p-of-<fn>
       (implies (sv::svexlist-p lst)
                (sv::svexlist-p res)))
     (defret integerp-of-<fn>-1
       (implies (integer-listp (sv::svexlist-eval$ lst env))
                (integer-listp (sv::svexlist-eval$ res env)))))

   (define svex-apply$-for-bitxor-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((equal arg1 0)
            arg2)
           ((equal arg2 0)
            arg1)
           (t (hons-list 'sv::bitxor arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                    (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitxor (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other))
            (equal (sv::4vec-bitxor other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitxor (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other)))
       :hints (("Goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitxor args)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 SV::SVEXLIST-EVAL$)
                                ()))))

     )

   (define svex-apply$-for-bitand-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((or (equal arg1 0)
                (equal arg2 0))
            0)
           ((equal arg2 -1)
            arg1)
           ((equal arg1 -1)
            arg2)
           (t (hons-list 'sv::bitand arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                    (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitand (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitand (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other))
            (equal (sv::4vec-bitand other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitand (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other)))
       :hints (("Goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitand args)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 SV::SVEXLIST-EVAL$)
                                ()))))

     )

   (define svex-apply$-for-bitor-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((or (equal arg1 -1)
                (equal arg2 -1))
            -1)
           ((equal arg1 0)
            arg2)
           ((equal arg2 0)
            arg1)
           (t (hons-list 'sv::bitor arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                   (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitor (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitor (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                                   (sv::svex-eval$ arg2 env))
                                   other))
            (equal (sv::4vec-bitor other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitor (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                                   (sv::svex-eval$ arg2 env))
                                   other)))
       :hints (("goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitor args))
                         (:free (x) (SV::4VEC-BITOR -1 x))
                         (:free (x) (SV::3VEC-BITOR -1 x)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 sv::svexlist-eval$)
                                ())))))

   )

  :returns (mv (res-svex sv::svex-p :hyp (and (sv::svex-p svex)
                                              (or (equal bit-fn 'sv::bitand)
                                                  (equal bit-fn 'sv::bitor)
                                                  (equal bit-fn 'sv::bitxor))))
               (remaining-to-remove sv::svexlist-p :hyp
                                    (and (sv::svexlist-p to-remove-lst)
                                         (or (equal bit-fn 'sv::bitand)
                                             (equal bit-fn 'sv::bitor)
                                             (equal bit-fn 'sv::bitxor)))))
  :verify-guards :after-returns

  (case-match svex
    ((fn x y)
     (b* (((unless (equal fn bit-fn))
           (if (svl::member-hons-equal svex to-remove-lst)
               (mv (if (eq bit-fn 'sv::bitand) -1 0)
                   (remove-equal-once svex to-remove-lst))
             (mv svex to-remove-lst)))
          (remove-x (svl::member-hons-equal x to-remove-lst))
          ((mv x to-remove-lst)
           (if remove-x
               (mv (if (eq bit-fn 'sv::bitand) -1 0)
                   (remove-equal-once x to-remove-lst))
             (careful-search-from-counterpart-svex-aux-remove x to-remove-lst)))
          (remove-y (svl::member-hons-equal y to-remove-lst))
          ((mv y to-remove-lst)
           (if remove-y
               (mv (if (eq bit-fn 'sv::bitand) -1 0)
                   (remove-equal-once y to-remove-lst))
             (careful-search-from-counterpart-svex-aux-remove y to-remove-lst))))
       (mv
        (cond ((eq bit-fn 'sv::bitand)
               (svex-apply$-for-bitand-meta x y))
              ((eq bit-fn 'sv::bitor)
               (svex-apply$-for-bitor-meta x y))
              (t
               (svex-apply$-for-bitxor-meta x y)))
        to-remove-lst)))
    (& (mv svex to-remove-lst)))
  ///

  (defret integerp-of-<fn>-1
    (implies (integer-listp (sv::svexlist-eval$ to-remove-lst env))
             (integer-listp (sv::svexlist-eval$ remaining-to-remove env))))

  (local
   (defthm svex-eval$-when-4vec-p
     (implies (sv::4vec-p x)
              (equal (sv::Svex-eval x env)
                     x))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-quote->val sv::Svex-eval sv::4vec-p) ())))))

  (local
   (defthm svex-eval$-bitxor-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env)
                                           (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitxor-lst lst env))
                   (equal (sv::4vec-bitxor (sv::Svex-eval$ x env)
                                           (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitxor-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitxor-lst)
                              ())))))

  (local
   (defthm svex-eval$-bitand-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst (remove-equal-once x lst) env)
                                           (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitand-lst lst env))
                   (equal (sv::4vec-bitand (sv::Svex-eval$ x env)
                                           (svl::svex-eval$-bitand-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitand-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitand-lst)
                              ())))))

  (local
   (defthm svex-eval$-bitor-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst (remove-equal-once x lst) env)
                                          (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitor-lst lst env))
                   (equal (sv::4vec-bitor (sv::Svex-eval$ x env)
                                          (svl::svex-eval$-bitor-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitor-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitor-lst)
                              ())))))

  (local
   (defthmd 4vec-bitxor-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitxor new a)
                     (sv::4vec-bitxor new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthmd 4vec-bitand-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitand new a)
                     (sv::4vec-bitand new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthmd 4vec-bitor-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitor new a)
                     (sv::4vec-bitor new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthm svex-eval$-bitxor-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env)
                                           other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst lst env)
                                      other)
                     (sv::4vec-bitxor (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitxor-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitxor-lst-of-remove-equal))))))

  (local
   (defthm svex-eval$-bitand-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst (remove-equal-once x lst) env)
                                           other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst lst env)
                                      other)
                     (sv::4vec-bitand (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitand-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitand-lst-of-remove-equal))))))

  (local
   (defthm svex-eval$-bitor-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst (remove-equal-once x lst) env)
                                          other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst lst env)
                                     other)
                     (sv::4vec-bitor (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitor-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitor-lst-of-remove-equal))))))

  (local
   (defthm bitxor-lemma
     (implies (and (equal (sv::4vec-bitxor a b)
                          (sv::4vec-bitxor x y))
                   (equal (sv::4vec-bitxor y 1z)
                          (sv::4vec-bitxor k m)))
              (equal (equal (sv::4vec-bitxor a (sv::4vec-bitxor b 1z))
                            (sv::4vec-bitxor x (sv::4vec-bitxor k m)))
                     t))))

  (local
   (defthm bitand-lemma
     (implies (and (equal (sv::4vec-bitand a b)
                          (sv::4vec-bitand x y))
                   (equal (sv::4vec-bitand y 1z)
                          (sv::4vec-bitand k m)))
              (equal (equal (sv::4vec-bitand a (sv::4vec-bitand b 1z))
                            (sv::4vec-bitand x (sv::4vec-bitand k m)))
                     t))))

  (local
   (defthm bitor-lemma
     (implies (and (equal (sv::4vec-bitor a b)
                          (sv::4vec-bitor x y))
                   (equal (sv::4vec-bitor y 1z)
                          (sv::4vec-bitor k m)))
              (equal (equal (sv::4vec-bitor a (sv::4vec-bitor b 1z))
                            (sv::4vec-bitor x (sv::4vec-bitor k m)))
                     t))))

  (local
   (defthm 3/4vec-p-of-svex-eval$-bitxor-lst
     (and (sv::3vec-p (svl::svex-eval$-bitxor-lst x env))
          (sv::4vec-p (svl::svex-eval$-bitxor-lst x env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitxor-lst) ())))))

  (local
   (defthm 3/4vec-p-of-svex-eval$-bitand-lst
     (and (sv::3vec-p (svl::svex-eval$-bitand-lst x env))
          (sv::4vec-p (svl::svex-eval$-bitand-lst x env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitand-lst) ())))))

  (local
   (defthm 3/4vec-p-of-svex-eval$-bitor-lst
     (and (sv::3vec-p (svl::svex-eval$-bitor-lst x env))
          (sv::4vec-p (svl::svex-eval$-bitor-lst x env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitor-lst) ())))))

  (defret <fn>-is-correct-for-bitxor
    (implies (equal bit-fn 'sv::Bitxor)
             (and (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                          (svl::svex-eval$-bitxor-lst to-remove-lst env))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitxor-lst remaining-to-remove env)))
                  (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                          (sv::svex-eval$ res-svex env))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitxor-lst remaining-to-remove env)))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitxor args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              SV::SVEXLIST-EVAL$)
                             ()))))

  (defret <fn>-is-correct-for-bitand
    (implies (equal bit-fn 'sv::bitand)
             (and (equal (sv::4vec-bitand (sv::svex-eval$ res-svex env)
                                          (svl::svex-eval$-bitand-lst to-remove-lst env))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitand-lst remaining-to-remove env)))
                  (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst to-remove-lst env)
                                          (sv::svex-eval$ res-svex env))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitand-lst remaining-to-remove env)))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitand args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              SV::SVEXLIST-EVAL$)
                             ()))))

  (defret <fn>-is-correct-for-bitor
    (implies (equal bit-fn 'sv::bitor)
             (and (equal (sv::4vec-bitor (sv::svex-eval$ res-svex env)
                                         (svl::svex-eval$-bitor-lst to-remove-lst env))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (svl::svex-eval$-bitor-lst remaining-to-remove env)))
                  (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst to-remove-lst env)
                                         (sv::svex-eval$ res-svex env))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (svl::svex-eval$-bitor-lst remaining-to-remove env)))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitor args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              sv::svexlist-eval$)
                             ()))))

  (defret <fn>-is-correct-for-bitxor-2
    (implies (equal bit-fn 'sv::Bitxor)
             (and (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                          (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                                           other))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst remaining-to-remove env)
                                                           other)))
                  (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                          (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                                           other))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst remaining-to-remove env)
                                                           other)))))
    :otf-flg t
    :hints (("Goal")))

  (defret <fn>-is-correct-for-bitand-2
    (implies (equal bit-fn 'sv::Bitand)
             (and (equal (sv::4vec-bitand (sv::svex-eval$ res-svex env)
                                          (sv::4vec-bitand (svl::svex-eval$-bitand-lst to-remove-lst env)
                                                           other))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (sv::4vec-bitand (svl::svex-eval$-bitand-lst remaining-to-remove env)
                                                           other)))
                  (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst to-remove-lst env)
                                          (sv::4vec-bitand (sv::svex-eval$ res-svex env)
                                                           other))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (sv::4vec-bitand (svl::svex-eval$-bitand-lst remaining-to-remove env)
                                                           other)))))
    :otf-flg t
    :hints (("Goal")))

  (defret <fn>-is-correct-for-bitor-2
    (implies (equal bit-fn 'sv::Bitor)
             (and (equal (sv::4vec-bitor (sv::svex-eval$ res-svex env)
                                         (sv::4vec-bitor (svl::svex-eval$-bitor-lst to-remove-lst env)
                                                         other))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (sv::4vec-bitor (svl::svex-eval$-bitor-lst remaining-to-remove env)
                                                         other)))
                  (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst to-remove-lst env)
                                         (sv::4vec-bitor (sv::svex-eval$ res-svex env)
                                                         other))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (sv::4vec-bitor (svl::svex-eval$-bitor-lst remaining-to-remove env)
                                                         other)))))
    :otf-flg t
    :hints (("Goal")))

  ;; measure lemmas:
  ;; not neaded as the caller of this function has a limit measure.
  #|(defret svex-count-of-<fn>
  (implies (or (equal bit-fn 'sv::bitand)
  (equal bit-fn 'sv::bitxor))
  (and (implies (equal remaining-to-remove to-remove-lst)
  (<= (sv::svex-count res-svex)
  (sv::svex-count svex)))
  (implies (not (equal remaining-to-remove to-remove-lst))
  (< (sv::svex-count res-svex)
  (sv::svex-count svex)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
  :in-theory (e/d (svex-apply$-for-bitxor-meta
  SV::SVEX-COUNT
  SV::SVEX-CALL->ARGS
  SV::SVEXlist-COUNT
  sv::Svex-kind)
  ()))))|#

  ;; (careful-search-from-counterpart-svex-aux-remove #!SV'(bitxor (bitxor a b) (bitxor c d)) #!SV'(a c))
  ;; ;; returns
  ;; ((SV::BITXOR SV::B SV::D) NIL)
  )

(define lst-to-bitxor/and-chain (lst
                                 &key
                                 ((bit-fn symbolp) 'bit-fn))
  :Returns (res sv::Svex-p :hyp (and (sv::svexlist-p lst)
                                     (or (equal bit-fn 'sv::bitand)
                                         (equal bit-fn 'sv::bitxor))))
  (if (atom lst)
      (if (eq bit-fn 'sv::bitand) -1 0)
    (if (atom (cdr lst))
        (car lst)
      (hons-list bit-fn (car lst)
                 (lst-to-bitxor/and-chain (cdr lst)))))
  ///
  (defret <fn>-correct-for-bitxor
    (implies (equal bit-fn 'sv::bitxor)
             (and (equal (sv::3vec-fix (sv::Svex-eval$ res env))
                         (svl::svex-eval$-bitxor-lst lst env))
                  (equal (sv::4vec-bitxor other (sv::Svex-eval$ res env))
                         (sv::4vec-bitxor other (svl::svex-eval$-bitxor-lst lst env)))
                  (equal (sv::4vec-bitxor (sv::Svex-eval$ res env) other)
                         (sv::4vec-bitxor other (svl::svex-eval$-bitxor-lst lst env)))))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-CALL->FN
                              SV::SVEX-APPLY
                              SV::SVEX-CALL->args)
                             ()))))
  (defret <fn>-correct-for-bitand
    (implies (equal bit-fn 'sv::bitand)
             (and (equal (sv::3vec-fix (sv::Svex-eval$ res env))
                         (svl::svex-eval$-bitand-lst lst env))
                  (equal (sv::4vec-bitand other (sv::Svex-eval$ res env))
                         (sv::4vec-bitand other (svl::svex-eval$-bitand-lst lst env)))
                  (equal (sv::4vec-bitand (sv::Svex-eval$ res env) other)
                         (sv::4vec-bitand other (svl::svex-eval$-bitand-lst lst env)))))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-CALL->FN
                              SV::SVEX-APPLY
                              SV::SVEX-CALL->args)
                             ())))))

(progn
  (local
   (defthm integerp-of-svex-eval$-bitxor-lst
     (implies (integer-listp (sv::svexlist-eval$ lst env))
              (integerp (svl::svex-eval$-bitxor-lst lst env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitxor-lst) ())))))

  (local
   (defthm integerp-of-svex-eval$-bitand-lst
     (implies (integer-listp (sv::svexlist-eval$ lst env))
              (integerp (svl::svex-eval$-bitand-lst lst env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitand-lst) ())))))

  (local
   (defthm integer-listp-of-svexlist-eval$-lemma
     (implies (and (integer-listp x))
              (integer-listp (sv::svexlist-eval$ x env)))
     :hints (("Goal"
              :in-theory (e/d (SV::SVEX-QUOTE->VAL) ()))))))


(progn
  (define already-parsed-svex-eval$-inv (alist env)
    :verify-guards nil
    (if (atom alist)
        (symbolp alist)
      (and (consp (car alist))
           (equal (sv::Svex-eval$ (caar alist) env)
                  (sv::Svex-eval$ (cdar alist) env))
           (already-parsed-svex-eval$-inv (cdr alist) env)))
    ///
    (defthm already-parsed-svex-eval$-inv-of-nil
      (implies (symbolp x)
               (equal (already-parsed-svex-eval$-inv x env) t)))

    (defthm already-parsed-svex-eval$-inv-of-cons
      (equal (already-parsed-svex-eval$-inv (cons (cons x y) rest) env)
             (and (equal (sv::Svex-eval$ x env)
                         (sv::Svex-eval$ y env))
                  (already-parsed-svex-eval$-inv rest env))))

    (defthm already-parsed-svex-eval$-inv-of-hons-assoc-equal
      (implies (and (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)
                    (already-parsed-svex-eval$-inv ALREADY-PARSED env))
               (equal (sv::Svex-eval$ (CDR (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)) env)
                      (sv::Svex-eval$ svex env)))))

  (define already-parsed-p (alist)
    (if (atom alist)
        (symbolp alist)
      (and (consp (car alist))
           (sv::Svex-p (caar alist))
           (sv::Svex-p (cdar alist))
           (already-parsed-p (cdr alist))))
    ///
    (defthm already-parsed-p-of-cons
      (equal (already-parsed-p (cons (cons x y) rest))
             (and (sv::Svex-p x)
                  (sv::Svex-p y)
                  (already-parsed-p rest))))

    (defthm already-parsed-p-of-hons-assoc-equal
      (implies (and (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)
                    (ALREADY-PARSED-P ALREADY-PARSED))
               (SV::SVEX-P (CDR (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)))))))


(defines careful-search-from-counterpart-svex-aux
  :verify-guards nil

  :prepwork ((Local
              (in-theory (enable sv::svex-call->fn)))

             (define careful-search-from-counterpart-svex-aux-counter ()
               nil
               ///
               (profile 'careful-search-from-counterpart-svex-aux-counter))

             (define svex-apply$-for-bitxor/and/or-meta2 (arg1 arg2
                                                               &key
                                                               ((bit-fn symbolp) 'bit-fn))
               :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                                       (force (sv::svex-p arg2))))
               :inline t
               (b* ((res
                     (cond ((equal bit-fn 'sv::bitand)
                            (cond ((or (equal arg1 0)
                                       (equal arg2 0))
                                   0)
                                  ((equal arg1 -1)
                                   (create-unfloat-for-adder-fnc  arg2))
                                  ((equal arg2 -1)
                                   (create-unfloat-for-adder-fnc  arg1))
                                  (t (hons-list 'sv::bitand arg1 arg2))))
                           ((equal bit-fn 'sv::bitor)
                            (cond ((or (equal arg1 -1)
                                       (equal arg2 -1))
                                   -1)
                                  ((equal arg1 0)
                                   (create-unfloat-for-adder-fnc  arg2))
                                  ((equal arg2 0)
                                   (create-unfloat-for-adder-fnc  arg1))
                                  (t (hons-list 'sv::bitor arg1 arg2))))
                           (t
                            (cond ((equal arg1 0)
                                   (create-unfloat-for-adder-fnc  arg2))
                                  ((equal arg2 0)
                                   (create-unfloat-for-adder-fnc  arg1))
                                  (t (hons-list 'sv::bitxor arg1 arg2))))))
                    ;; TODO: clean ones in a better way here...
                    ;;(res (case-match res (('sv::bitxor 1 ('sv::bitxor 1 x)) x) (& res)))
                    )
                 res)
               ///
               (defret <fn>-is-correct
                 (implies (warrants-for-adder-pattern-match)
                          (equal (sv::svex-eval$ res-svex env)
                                 (cond ((equal bit-fn 'sv::bitand)
                                        (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                                         (sv::svex-eval$ arg2 env)))
                                       ((equal bit-fn 'sv::bitor)
                                        (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                                        (sv::svex-eval$ arg2 env)))
                                       (t
                                        (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                         (sv::svex-eval$ arg2 env))))))
                 :hints (("Goal"
                          :expand ((:free (args)
                                          (sv::svex-apply 'sv::bitxor args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::bitand args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::bitor args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::unfloat args))
                                   (:free (x)
                                          (sv::4vec-bitor -1 x))
                                   (:free (x)
                                          (sv::3vec-bitor -1 x)))
                          :in-theory (e/d (sv::svex-call->fn
                                           sv::svex-call->args
                                           SV::SVEXLIST-EVAL$)
                                          ()))))

               )

             (define find-s-from-found-c-bitxor/and-args (args
                                                          &key
                                                          ((bit-fn symbolp) 'bit-fn))
               :returns (res sv::svex-p :hyp (and (force (sv::Svexlist-p args))
                                                  (or (equal bit-fn 'sv::bitand)
                                                      (equal bit-fn 'sv::bitor)
                                                      (equal bit-fn 'sv::bitxor))))
               (cond
                ((atom args)
                 (if (equal bit-fn 'sv::bitand) -1 0))
                ((atom (cdr args))
                 (create-unfloat-for-adder-fnc (car args)))
                ((atom (cddr args))
                 (hons-list bit-fn
                            (car args)
                            (cadr args)))
                (t
                 (hons-list bit-fn
                            (find-s-from-found-c-bitxor/and-args (cdr args))
                            (car args))))
               ///
               (defret <fn>-is-correct
                 (implies (warrants-for-adder-pattern-match)
                          (and (implies (equal bit-fn 'sv::bitand)
                                        (equal (sv::Svex-eval$ res env)
                                               (svl::svex-eval$-bitand-lst args env)))
                               (implies (equal bit-fn 'sv::bitxor)
                                        (equal (sv::Svex-eval$ res env)
                                               (svl::svex-eval$-bitxor-lst args env)))
                               (implies (equal bit-fn 'sv::bitor)
                                        (equal (sv::Svex-eval$ res env)
                                               (svl::svex-eval$-bitor-lst args env)))))
                 :hints (("Goal"
                          :in-theory (e/d (SV::SVEX-CALL->FN
                                           SV::SVEX-CALL->args
                                           SV::SVEX-APPLY)
                                          ()))))))

  (define careful-search-from-counterpart-svex-aux ((svex sv::svex-p)
                                                    (exploded-args-and-args-alist exploded-args-and-args-alist-p)
                                                    &key
                                                    ((already-parsed already-parsed-p) 'already-parsed)
                                                    ((adder-type symbolp) 'adder-type)
                                                    ((config svl::svex-reduce-config-p) 'config)
                                                    ((column acl2::maybe-integerp) 'column)
                                                    ((limit natp) 'limit))
    ;;:measure (sv::Svex-count svex)
    :measure (nfix limit)
    :returns (mv (res)
                 (res-already-parsed))
    :no-function t
    (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
        (mv svex already-parsed)
      (let ((limit (1- limit)))
        (sv::svex-case
         svex
         :quote (mv svex already-parsed)
         :var   (mv svex already-parsed)
         :call
         (b* ((parsed? (hons-get svex already-parsed))
              ((when parsed?)
               (mv (cdr parsed?) already-parsed))
              ((when (and*-exec column
                                (eq svex.fn 'sv::concat)
                                (svl::equal-len svex.args 3)
                                (natp (first svex.args))))
               (b* ((size (first svex.args))
                    ((mv second already-parsed)
                     (careful-search-from-counterpart-svex-aux (second svex.args) exploded-args-and-args-alist))
                    ((mv third already-parsed)
                     (careful-search-from-counterpart-svex-aux (third svex.args) exploded-args-and-args-alist
                                                               :column (+ column size)))
                    (res (hons-list 'sv::concat size second third)))
                 (mv res
                     (hons-acons svex res already-parsed))))

              ((unless (cond ((eq adder-type 'ha-c) (bitand-pattern-p svex))
                             ((eq adder-type 'ha+1-c) (bitor-pattern-p svex))
                             (t (bitxor-pattern-p svex))))
               (b* (;; bitand  and bitor is likely a part  of carry logic. This
                    ;; will  mess up  with column  calculation.  So  let's just
                    ;; increase column a lot so it gets thrown away.
                    ((when (and*-exec column
                                      (member-eq svex.fn '(sv::bitand sv::bitor))))
                     (mv svex already-parsed))
                    ;; under a carry, we will know to be checking a previous column.
                    ;; this is not a great system though...
                    (column (and*-exec column
                                       (- column
                                          (acl2::bool->bit
                                           (member-eq svex.fn '(ha-c-chain fa-c-chain ha+1-c-chain))))))
                    ((mv args already-parsed)
                     (careful-search-from-counterpart-svexlist-aux svex.args exploded-args-and-args-alist))
                    (res (sv::svex-call svex.fn args)))
                 (mv res (hons-acons svex res already-parsed))))

              (bit-fn svex.fn)

              ;; first see if anything in the xor chain appears as an argument to an orphan fa-c
              ;; explore1-res will be list of all 3 args. or 2 args if working for ha-c
              ((exploded-args-and-args x)
               (careful-search-from-counterpart-svex-aux-explore svex exploded-args-and-args-alist nil))

              ((unless (and*-exec x.args x.exploded-args))
               (b* (((mv args already-parsed)
                     (careful-search-from-counterpart-svexlist-aux svex.args exploded-args-and-args-alist))
                    (res (sv::svex-call svex.fn args)))
                 (mv res (hons-acons svex res already-parsed))))

              ((mv rest-bitxor/and remaining-exploded-args)
               (careful-search-from-counterpart-svex-aux-remove svex x.exploded-args))

              ((unless (and*-exec
                        (implies (equal adder-type 'ha-c) ;; do not allow borrowing elements for ha-c..
                                 (not remaining-exploded-args))
                        (implies (equal adder-type 'ha+1-c) ;; do not allow borrowing elements for ha+1-c..
                                 (not remaining-exploded-args))
                        (integer-listp remaining-exploded-args)

                        ;; what that extra elements are allowed os controlled in careful-search-from-counterpart-svex-aux-explore2
                        ;; restriction is integer-listp because only then repeated elements in bitxor are simplified away to 0.
                        ))
               ;; this should never happend (hopefully?)
               (b* (((mv args already-parsed)
                     (careful-search-from-counterpart-svexlist-aux svex.args exploded-args-and-args-alist))
                    (res (sv::svex-call svex.fn args)))
                 (mv res (hons-acons svex res already-parsed))))

              (rest-bitxor/and (if remaining-exploded-args
                                   (svex-apply$-for-bitxor/and/or-meta2
                                    ;; 1 comes from the only allowed value of remaining-exploded-args.
                                    ;; possibly, this can be extended to anything..
                                    (lst-to-bitxor/and-chain remaining-exploded-args)
                                    rest-bitxor/and)
                                 rest-bitxor/and))

              (- (careful-search-from-counterpart-svex-aux-counter))
              ((mv rest1 already-parsed)
               (careful-search-from-counterpart-svex-aux rest-bitxor/and exploded-args-and-args-alist))
              ((mv args already-parsed)
               (careful-search-from-counterpart-svexlist-aux x.args exploded-args-and-args-alist))
              (result
               (svex-apply$-for-bitxor/and/or-meta2 rest1 (find-s-from-found-c-bitxor/and-args args))))
           (mv result (hons-acons svex result already-parsed)))))))

  (define careful-search-from-counterpart-svexlist-aux ((lst sv::Svexlist-p)
                                                        (exploded-args-and-args-alist
                                                         exploded-args-and-args-alist-p)
                                                        &key
                                                        ((already-parsed already-parsed-p) 'already-parsed)
                                                        ((adder-type symbolp) 'adder-type)
                                                        ((config svl::svex-reduce-config-p) 'config)
                                                        ((column acl2::maybe-integerp) 'column)
                                                        ((limit natp) 'limit))
    ;;:measure (sv::svexlist-count lst)
    :measure (nfix limit)
    :returns (mv (res-lst)
                 (res-already-parsed))
    :no-function t
    (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
        (mv lst already-parsed)
      (let ((limit (1- limit)))
        (if (atom lst)
            (mv nil already-parsed)
          (b* (((mv cur already-parsed) (careful-search-from-counterpart-svex-aux (car lst) exploded-args-and-args-alist))
               ((mv res already-parsed) (careful-search-from-counterpart-svexlist-aux (cdr lst) exploded-args-and-args-alist)))
            (mv (hons cur res) already-parsed))))))
  ///

  (local
   (in-theory (disable acl2::bool->bit
                       MEMBER-EQUAL)))

  (defret-mutual return-type-of-<fn>
    (defret return-type-of-<fn>
      (implies (and (sv::Svex-p svex)
                    (exploded-args-and-args-alist-p exploded-args-and-args-alist)
                    (already-parsed-p already-parsed))
               (and (sv::svex-p res)
                    (already-parsed-p res-already-parsed)))
      :fn careful-search-from-counterpart-svex-aux)
    (defret return-type-of-<fn>
      (implies (and (sv::Svexlist-p lst)
                    (exploded-args-and-args-alist-p exploded-args-and-args-alist)
                    (already-parsed-p already-parsed))
               (and (sv::Svexlist-p res-lst)
                    (already-parsed-p res-already-parsed)))
      :fn careful-search-from-counterpart-svexlist-aux))

  (local
   (defthm bitxor-pattern-of-svex-call-of-bitxor
     (bitxor-pattern-p (sv::svex-call 'sv::bitxor
                                      (list x y)))
     :hints (("Goal"
              :in-theory (e/d (SV::SVEX-CALL bitxor-pattern-p) ())))))

  (local
   (defthm bitand-pattern-of-svex-call-of-bitxor
     (bitand-pattern-p (sv::svex-call 'sv::bitand
                                      (list x y)))
     :hints (("Goal"
              :in-theory (e/d (SV::SVEX-CALL bitand-pattern-p) ())))))

  (local
   (defthm bitor-pattern-of-svex-call-of-bitor
     (bitor-pattern-p (sv::svex-call 'sv::bitor (list x y)))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-call bitor-pattern-p) ())))))

  (verify-guards careful-search-from-counterpart-svex-aux-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))

  ;;(memoize 'careful-search-from-counterpart-svex-aux-fn :condition '(eq (sv::svex-kind svex) :call))

  #|(acl2::memoize-partial
  ((careful-search-from-counterpart-svex-aux* careful-search-from-counterpart-svex-aux-fn)
  (careful-search-from-counterpart-svexlist-aux* careful-search-from-counterpart-svexlist-aux-fn
  :condition nil)))|#

  (local
   (include-book "std/basic/inductions" :DIR :SYSTEM))

  (local
   (defthmd svex-eval$-bitxor-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitxor-lst lst1 env)
                     (svl::svex-eval$-bitxor-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((SV::SVEXLIST-EVAL$ LST2 ENV))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitxor-lst)
                              ())))))

  (local
   (defthmd svex-eval$-bitand-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitand-lst lst1 env)
                     (svl::svex-eval$-bitand-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((SV::SVEXLIST-EVAL$ LST2 ENV))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitand-lst)
                              ())))))

  (local
   (defthmd svex-eval$-bitor-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitor-lst lst1 env)
                     (svl::svex-eval$-bitor-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((sv::svexlist-eval$ lst2 env))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitor-lst)
                              ())))))

  (local
   (defret svex-eval$-bitxor-lst-when-svexlist-evals-are-equal-special
     (implies (equal (sv::svexlist-eval$ res-lst env)
                     (sv::svexlist-eval$ lst env))
              (equal (svl::svex-eval$-bitxor-lst res-lst env)
                     (svl::svex-eval$-bitxor-lst lst env)))
     :fn careful-search-from-counterpart-svexlist-aux
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-bitxor-lst-when-svexlist-evals-are-equal) ())))))

  (local
   (defret svex-eval$-bitand-lst-when-svexlist-evals-are-equal-special
     (implies (equal (sv::svexlist-eval$ res-lst env)
                     (sv::svexlist-eval$ lst env))
              (equal (svl::svex-eval$-bitand-lst res-lst env)
                     (svl::svex-eval$-bitand-lst lst env)))
     :fn careful-search-from-counterpart-svexlist-aux
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-bitand-lst-when-svexlist-evals-are-equal) ())))))

  (local
   (defret svex-eval$-bitor-lst-when-svexlist-evals-are-equal-special
     (implies (equal (sv::svexlist-eval$ res-lst env)
                     (sv::svexlist-eval$ lst env))
              (equal (svl::svex-eval$-bitor-lst res-lst env)
                     (svl::svex-eval$-bitor-lst lst env)))
     :fn careful-search-from-counterpart-svexlist-aux
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-bitor-lst-when-svexlist-evals-are-equal) ())))))

  (defret-mutual <fn>-correct
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-p svex))
                    (force (warrants-for-adder-pattern-match))
                    (force (exploded-args-and-args-alist-p exploded-args-and-args-alist))
                    (force (exploded-args-and-args-alist-inv
                            exploded-args-and-args-alist env
                            :bit-fn (cond ((equal adder-type 'ha-c) 'sv::bitand)
                                          ((equal adder-type 'ha+1-c) 'sv::bitor)
                                          (t 'sv::bitxor))))
                    (force (already-parsed-svex-eval$-inv already-parsed env))
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    )
               (and (equal (sv::svex-eval$ res env)
                           (sv::svex-eval$ svex env))
                    (already-parsed-svex-eval$-inv res-already-parsed env)))
      :fn careful-search-from-counterpart-svex-aux)
    (defret <fn>-is-correct
      (implies (and (force (sv::svexlist-p lst))
                    (force (warrants-for-adder-pattern-match))
                    (force (exploded-args-and-args-alist-p exploded-args-and-args-alist))
                    (force (exploded-args-and-args-alist-inv
                            exploded-args-and-args-alist
                            env
                            :bit-fn (cond ((equal adder-type 'ha-c) 'sv::bitand)
                                          ((equal adder-type 'ha+1-c) 'sv::bitor)
                                          (t 'sv::bitxor))))
                    (force (already-parsed-svex-eval$-inv already-parsed env))
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config)))
               (and (equal (sv::svexlist-eval$ res-lst env)
                           (sv::svexlist-eval$ lst env))
                    (already-parsed-svex-eval$-inv res-already-parsed env)))
      :fn careful-search-from-counterpart-svexlist-aux)
    :otf-flg t
    :hints (("goal"
             :expand ((:free (x) (sv::svex-apply$ 'fa-s-chain x))
                      (:free (x) (sv::svex-apply$ 'ha-c-chain x))
                      (:free (x) (sv::svex-apply$ 'sv::bitxor x))
                      (:free (x) (sv::svex-apply 'sv::bitxor x))
                      (:free (x) (sv::svex-apply 'sv::bitor x))
                      (:free (x) (sv::svex-apply 'sv::bitand x))
                      (sv::svexlist-eval$ (cdr svex) env)
                      (sv::svexlist-eval$ (cddr svex) env)
                      (careful-search-from-counterpart-svexlist-aux  lst exploded-args-and-args-alist)
                      (careful-search-from-counterpart-svex-aux  svex exploded-args-and-args-alist)
                      )
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              sv::svexlist-eval$
                              fa-s-chain
                              ha-c-chain
                              ACL2::MERGE-SORT-LEXORDER
                              ACL2::MERGE-LEXORDER)
                             (integer-listp
                              sv::svexlist-eval$-when-consp
                              acl2::integer-listp-of-cons))))))

(define careful-search-from-counterpart-svex-alist ((alist sv::svex-alist-p)
                                                    (exploded-args-and-args-alist exploded-args-and-args-alist-p)
                                                    &key
                                                    ((already-parsed already-parsed-p) ''careful-search-from-counterpart-svex-alist)
                                                    ((adder-type symbolp) 'adder-type)
                                                    (track-column? 'track-column?)
                                                    ((config svl::svex-reduce-config-p) 'config))
  :returns (mv res res-already-parsed)
  :verify-guards nil
  (if (atom alist)
      (mv nil (progn$ ;; (cw "(len already-parsed): ~p0~%" (len already-parsed))
               ;; (cw "(len cleaned already-parsed): ~p0~%" (len (fast-alist-clean already-parsed)))
               (fast-alist-free already-parsed)))
    (b* ((column (and track-column? 0))
         ((mv x already-parsed)
          (careful-search-from-counterpart-svex-aux (cdar alist) exploded-args-and-args-alist :limit (expt 2 20)))
         ((mv rest already-parsed)
          (careful-search-from-counterpart-svex-alist (cdr alist) exploded-args-and-args-alist :already-parsed already-parsed)))
      (mv (acons (caar alist) x rest) already-parsed)))
  ///

  (defret return-val-of-<fn>
    (implies (and (sv::Svex-alist-p alist)
                  (exploded-args-and-args-alist-p exploded-args-and-args-alist)
                  (already-parsed-p already-parsed))
             (and (sv::Svex-alist-p res)
                  (alistp res)
                  (already-parsed-p res-already-parsed))))

  (verify-guards careful-search-from-counterpart-svex-alist-fn)

  (defret <fn>-is-correct
    (implies (and (force (sv::svex-alist-p alist))
                  (force (warrants-for-adder-pattern-match))
                  (force (exploded-args-and-args-alist-p exploded-args-and-args-alist))
                  (force (exploded-args-and-args-alist-inv
                          exploded-args-and-args-alist env
                          :bit-fn (cond ((equal adder-type 'ha-c) 'sv::bitand)
                                        ((equal adder-type 'ha+1-c) 'sv::bitor)
                                        (t 'sv::bitxor))))
                  (force (already-parsed-svex-eval$-inv already-parsed env))
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config)))
             (and (equal (sv::svex-alist-eval$ res env)
                         (sv::svex-alist-eval$ alist env))
                  (already-parsed-svex-eval$-inv res-already-parsed env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
