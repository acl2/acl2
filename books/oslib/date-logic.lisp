; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>
; Contributing author: Grant Jurgensen <grant@kestrel.edu>

(in-package "OSLIB")
(include-book "read-acl2-oracle")
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/define" :dir :system)
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (xdoc::set-default-parents oslib))

;; These return theorems are justified by the specification for
;; - decoded time: https://www.lispworks.com/documentation/HyperSpec/Body/25_ada.htm
;; - time zone: https://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#time_zone
(define get-decoded-time$ (state)
  :returns (mv (second natp :rule-classes :type-prescription)
               (minute natp :rule-classes :type-prescription)
               (hour natp :rule-classes :type-prescription)
               (date posp :rule-classes :type-prescription)
               (month posp :rule-classes :type-prescription)
               (year natp :rule-classes :type-prescription)
               (day natp :rule-classes :type-prescription)
               daylight-p
               (zone rationalp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current time represented as a decoded time."

  :long "<p>This is a wrapper to the standard @('get-decoded-time') Common Lisp
function.  In the logic, this is modeled as a read from the ACL2 oracle.</p>

<p>There are nine return values in addition to @('state'):</p>
<ul>
  <li>@('second') &mdash; A natural number less than @('60').</li>
  <li>@('minute') &mdash; A natural number less than @('60').</li>
  <li>@('hour') &mdash; A natural number less than @('24').</li>
  <li>@('date') &mdash; A positive natural number less than @('32').  This
    represents the day of the month.</li>
  <li>@('month') &mdash; A positive natural number less than @('13').  January
    is @('1'), February is @('2'), etc.</li>
  <li>@('year') &mdash; A natural number representing the year A.D.</li>
  <li>@('day') &mdash; A natural number less than @('7').  This represents the
    day of the week.  Monday is @('0'), Tuesday is @('1'), etc.</li>
  <li>@('daylight-p') &mdash; A generalized boolean indicating whether daylight
     savings time is active.</li>
  <li>@('zone') &mdash; A rational number between @('-24') and @('24')
    (inclusive).  This represents the number of hours <i>west</i> of GMT.  This
    value will be a multiple of @('1/3600') (i.e. a granularity of one
    second).  This value is <i>not</i> dependent on @('daylight-p').  E.g.,
    the value @('6') always represents central time (either Central Standard
    Time or Central Daylight Time depending on @('daylight-p')).  See
    @(tsee time-zone-abbreviation) for an example of the use of this value.</li>
</ul>

<p>See also @(see universal-time), which returns an integer representation of
the current time.</p>"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (equal (len val) 9)
             (integer-range-p 0 60 (first val))
             (integer-range-p 0 60 (second val))
             (integer-range-p 0 24 (third val))
             (integer-range-p 1 32 (fourth val))
             (integer-range-p 1 13 (fifth val))
             (natp (sixth val))
             (integer-range-p 0 7 (seventh val))
             (rationalp (ninth val))
             (<= -24 (ninth val))
             (<= (ninth val) 24)
             (equal (mod (ninth val) 1/3600) 0))
        (mv (first val)
            (second val)
            (third val)
            (fourth val)
            (fifth val)
            (sixth val)
            (seventh val)
            (eighth val)
            (ninth val)
            state)
      (mv 0 0 0 1 1 0 0 nil 0 state)))
  ///

  (defret get-decoded-time$.second-linear
    (< second 60)
    :rule-classes :linear)

  (defret get-decoded-time$.minute-linear
    (< minute 60)
    :rule-classes :linear)

  (defret get-decoded-time$.hour-linear
    (< hour 24)
    :rule-classes :linear)

  (defret get-decoded-time$.date-linear
    (< date 32)
    :rule-classes :linear)

  (defret get-decoded-time$.month-linear
    (< month 13)
    :rule-classes :linear)

  (defret get-decoded-time$.day-linear
    (< day 7)
    :rule-classes :linear)

  (defret get-decoded-time$.zone-min-linear
    (<= -24 zone)
    :rule-classes :linear)

  (defret get-decoded-time$.zone-max-linear
    (<= zone 24)
    :rule-classes :linear)

  (defret mod-of-get-decoded-time$.zone-and-1/3600
    (equal (mod zone 1/3600)
           0)))

(define universal-time (&optional (state 'state))
  :returns (mv (seconds natp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current timestamp as a natural number, specifically the
number of seconds since 00:00 January 1, 1900 GMT.  Note well that this is
<b>not</b> the Unix epoch."

  :long "<p>In the logic this function reads from the ACL2 oracle, so there is
no logical guarantee that it will return successive times.  (Indeed, the user
could likely change their computer's clock so that it would report earlier
times.)</p>

<p>In the execution, we use Common Lisp's @('get-universal-time') function to
figure out the current time in seconds since the start of 1900.</p>

<p>This is, for whatever reason, a different starting date than the Unix
epoch (which records time since the start of 1970).  You should therefore be
careful if you need to compare this timestamp against those produced by
external tools.</p>"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (natp val))
        (mv val state)
      (mv 0 state))))

(define time-zone-to-utc-string ((zone rationalp))
  (declare (xargs :split-types t)
           (type rational zone))
  :parents (get-decoded-time$)
  :short "Convert a time zone to a UTC offset string."

  :long "<p>See @(tsee get-decoded-time$) for a description of time zone
values.</p>"

  (let* ((sign (if (<= zone 0) "+" "-"))
         (total-minutes (abs (floor (* zone 60) 1)))
         (hours (floor total-minutes 60))
         (minutes (mod total-minutes 60)))
    (str::cat "UTC"
              sign
              (str::natstr (floor hours 10))
              (str::natstr (mod hours 10))
              ":"
              (str::natstr (floor minutes 10))
              (str::natstr (mod minutes 10))))
  :prepwork ((local (include-book "kestrel/arithmetic-light/floor" :dir :system))
             (local (include-book "kestrel/arithmetic-light/mod" :dir :system))))

(define time-zone-abbreviation ((zone rationalp) daylight-p)
  (declare (xargs :split-types t)
           (type rational zone))
  :parents (get-decoded-time$)
  :short "Convert a time zone to an abbreviation string."

  :long "<p>This will map certain time zone values to abbreviations.  There are
many time zone values which correspond to multiple time zones.  The choice of
mapped time zone is therefore largely arbitrary.  Time zone values which are
not mapped are instead rendered as a UTC offset. See
@(tsee time-zone-to-utc-string).</p>

<p>See @(tsee get-decoded-time$) for a description of time zone
values.</p>"

  (case zone
    ;; Note: Common Lisp time zones proceed *west* from GMT. Therefore, a
    ;; negative value like -14 represents a positive UTC offset, UTC+14.
    (-14 "LINT")        ; Line Islands Time
    (-12 (if daylight-p
             "NZDT"     ; New Zealand Daylight Time
           "NZST"))     ; New Zealand Standard Time
    (-11 "SBT")         ; Solomon Islands Time
    (-10 (if daylight-p
             "AEDT"     ; Australian Eastern Daylight Time
           "AEST"))     ; Australian Eastern Standard Time
    (-19/2 (if daylight-p
               "ACDT"   ; Australian Central Daylight Time
             "ACST"))   ; Australian Central Standard Time
    (-9 "JST")          ; Japan Standard Time
    (-8 (if daylight-p
            "CST China" ; China Standard Time
          "AWST"))      ; Australian Western Standard Time
    (-7 "WIB")          ; Western Indonesia Time
    (-13/2 "MMT")       ; Myanmar Time
    (-6 "BST")          ; Bangladesh Standard Time
    (-23/4 "NPT")       ; Nepal Time
    (-11/2 "IST")       ; India Standard Time
    (-5 "PKT")          ; Pakistan Standard Time
    (-9/2 "AFT")        ; Afghanistan Time
    (-4 "GST")          ; Gulf Standard Time
    (-7/2 "IRST")       ; Iran Standard Time
    (-3 "MSK")          ; Moscow Time
    (-2 (if daylight-p
            "EEST"      ; Eastern European Summer Time
          "EET"))       ; Eastern European Time
    (-1 (if daylight-p
            "CEST"      ; Central European Summer Time
          "CET"))       ; Central European Time
    (0 "GMT")           ; Greenwich Mean Time
    (1 "AZOT")          ; Azores Time
    (2 "GST")           ; South Georgia Time
    (3 "BRT")           ; Brasília Time
    (7/2 (if daylight-p
             "NDT"      ; Newfoundland Daylight Time
           "NST"))      ; Newfoundland Standard Time
    (4 (if daylight-p
           "ADT"        ; Atlantic Daylight Time
         "AST"))        ; Atlantic Standard Time
    (5 (if daylight-p
           "EDT"        ; Eastern Daylight Time
         "EST"))        ; Eastern Standard Time
    (6 (if daylight-p
           "CDT"        ; Central Daylight Time
         "CST"))        ; Central Standard Time
    (7 (if daylight-p
           "MDT"        ; Mountain Daylight Time
         "MST"))        ; Mountain Standard Time
    (8 (if daylight-p
           "PDT"        ; Pacific Daylight Time
         "PST"))        ; Pacific Standard Time
    (9 (if daylight-p
           "AKDT"       ; Alaska Daylight Time
         "AKST"))       ; Alaska Standard Time
    (10 "HST")          ; Hawaii-Aleutian Standard Time
    (11 "SST")          ; Samoa Standard Time
    (12 "BIT")          ; Baker Island Time
    (otherwise (time-zone-to-utc-string zone))))

(define date (&optional (state 'state) &key (zone 'nil))
  :returns (mv (datestamp stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current datestamp, like \"November 17, 2010 10:25:33\"."

  :long "<p>The datestamp string is constructed from the values returned by
@(tsee get-decoded-time$).  Optionally, specify @(':zone t') to include a time
zone abbreviation in the datestamp.  (The default is no time zone.)</p>

<p>See also @(see universal-time), which returns an integer representation of
the current time.</p>"

  (mv-let (second minute hour date month year day daylight-p zone-code state)
          (get-decoded-time$ state)
    (declare (ignore day))
    (let ((month (nth (- month 1) '("January" "February" "March" "April" "May"
                                    "June" "July" "August" "September" "October"
                                    "November" "December")))
          (year   (str::natstr year))
          (date   (str::natstr date))
          (hour   (if (< hour 10)
                      (str::cat "0" (str::natstr hour))
                    (str::natstr hour)))
          (minute (if (< minute 10)
                      (str::cat "0" (str::natstr minute))
                    (str::natstr minute)))
          (second (if (< second 10)
                      (str::cat "0" (str::natstr second))
                    (str::natstr second))))
      (mv (str::cat month
                    " "
                    date
                    ", "
                    year
                    " "
                    hour
                    ":"
                    minute
                    ":"
                    second
                    (if zone
                        (str::cat " "
                                  (time-zone-abbreviation zone-code daylight-p))
                      ""))
          state))))
