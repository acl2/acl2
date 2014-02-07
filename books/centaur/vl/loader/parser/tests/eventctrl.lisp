; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "base")
(include-book "../eventctrl")

(assert!
 (b* ((tokens (make-test-tokens "@(foo or bar or baz)"))
      (warnings 'blah-warnings)
      (config   *vl-default-loadconfig*)
      ((mv err val tokens warnings)
       (vl-parse-delay-or-event-control)))
   (and (not err)
        (not tokens)
        (equal warnings 'blah-warnings)
        (equal val (make-vl-eventcontrol
                    :starp nil
                    :atoms
                    (list (make-vl-evatom
                           :type :vl-noedge
                           :expr (make-vl-atom :guts (vl-id "foo")))
                          (make-vl-evatom
                           :type :vl-noedge
                           :expr (make-vl-atom :guts (vl-id "bar")))
                          (make-vl-evatom
                           :type :vl-noedge
                           :expr (make-vl-atom :guts (vl-id "baz")))))))))

(assert!
 (b* ((tokens (make-test-tokens "@(posedge foo)"))
      (warnings 'blah-warnings)
      (config   *vl-default-loadconfig*)
      ((mv err val tokens warnings)
       (vl-parse-delay-or-event-control)))
   (and (not err)
        (not tokens)
        (equal warnings 'blah-warnings)
        (equal val (make-vl-eventcontrol
                    :starp nil
                    :atoms (list (make-vl-evatom
                                  :type :vl-posedge
                                  :expr (make-vl-atom :guts (vl-id "foo")))))))))

(assert!
 (b* ((tokens   (make-test-tokens "@(negedge foo)"))
      (warnings 'blah-warnings)
      (config   *vl-default-loadconfig*)
      ((mv err val tokens warnings)
       (vl-parse-delay-or-event-control)))
   (and (not err)
        (not tokens)
        (equal warnings 'blah-warnings)
        (equal val (make-vl-eventcontrol
                    :starp nil
                    :atoms (list (make-vl-evatom
                                  :type :vl-negedge
                                  :expr (make-vl-atom :guts (vl-id "foo")))))))))

(assert! (b* ((tokens   (make-test-tokens "@*"))
              (warnings 'blah-warnings)
              (config   *vl-default-loadconfig*)
              ((mv err val tokens warnings)
               (vl-parse-delay-or-event-control)))
           (and (not err)
                (not tokens)
                (equal warnings 'blah-warnings)
                (equal val (make-vl-eventcontrol
                            :starp t
                            :atoms nil)))))

(assert! (b* ((tokens   (make-test-tokens "@(*)"))
              (warnings 'blah-warnings)
              (config   *vl-default-loadconfig*)
              ((mv err val tokens warnings)
               (vl-parse-delay-or-event-control)))
           (and (not err)
                (not tokens)
                (equal warnings 'blah-warnings)
                (equal val (make-vl-eventcontrol
                            :starp t
                            :atoms nil)))))

(assert! (b* (((mv err val tokens warnings)
               (vl-parse-delay-or-event-control
                :tokens (make-test-tokens "@( *)")
                :warnings 'blah-warnings
                :config *vl-default-loadconfig*)))
           (and (not err)
                (not tokens)
                (equal warnings 'blah-warnings)
                (equal val (make-vl-eventcontrol
                            :starp t
                            :atoms nil)))))

(assert! (b* (((mv err val tokens warnings)
               (vl-parse-delay-or-event-control
                :tokens (make-test-tokens "@(* )")
                :warnings 'blah-warnings
                :config *vl-default-loadconfig*)))
           (and (not err)
                (not tokens)
                (equal warnings 'blah-warnings)
                (equal val (make-vl-eventcontrol
                            :starp t
                            :atoms nil)))))

(assert! (b* (((mv err val tokens warnings)
               (vl-parse-delay-or-event-control
                :tokens (make-test-tokens "@( * )")
                :warnings 'blah-warnings
                :config *vl-default-loadconfig*)))
           (and (not err)
                (not tokens)
                (equal warnings 'blah-warnings)
                (equal val (make-vl-eventcontrol
                            :starp t
                            :atoms nil)))))

