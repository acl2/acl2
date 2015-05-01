; SATLINK - Link from ACL2 to SAT Solvers
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "SATLINK")
(include-book "top")
(include-book "std/util/defconsts" :dir :system)

(defxdoc gather-benchmarks
  :parents (satlink)
  :short "A @(see satlink) plugin for saving problems and storing them in
@('satlink-benchmarks') directories."

  :long "<p>This Satlink plugin can be used to automatically collect up all
problems given to Satlink into @('satlink-benchmarks') directories.  These
files might be useful for benchmarking or testing SAT solvers.</p>

<p>To use the plugin, simply include the following book:</p>

@({
    (include-book \"centaur/satlink/benchmarks\" :dir :system)
})

<p>and invoke Satlink as normal.  For instance, if you have a collection of
@(see acl2::books) that use @(see acl2::gl) in Satlink mode to prove some
theorems, then adding the above @('include-book') should allow you to gather up
all of the SAT problems that GL solves during the course of certifying your
books.</p>

<p>This plugin saves SAT problems into the @('./satlink-benchmarks') directory,
relative to wherever you are running the tests.  That is, if you many different
directories with their own GL/Satlink-based proofs, you'll get multiple
@('satlink-benchmarks') directories spread out throughout your file system.</p>

<p>The resulting files are in DIMACS format and have ugly names like:</p>

<ul>
<li>xzsVtfY_tkY72RMcmmAkOw.sat</li>
<li>Y5fvIdHKoF_5ZPLjF75gCg.unsat</li>
</ul>

<p>The extension says whether the problem was satisfiable or unsatisfiable.
The file names are generated using an md5sum of the contents of the file.
Although they are ugly, this scheme (practically speaking) ensures that:</p>

<ul>

<li>We don't gather multiple copies of identical problems.  That is, if we
certify and then re-certify the same books multiple times, the problems that GL
gives to Satlink will be the same each time, so we'll overwrite the previous
benchmarks with copies of themselves.</li>

<li>We don't have to coordinate between multiple machines that are solving
benchmarks in parallel and writing to the same NFS-mounted directory.  That is,
we never have to ask a question like: what's the next free file name?</li>

<li>We <i>do</i> gather any variants of the same proof over time.  That is, as
the design evolves, or as the spec changes, or as GL/ESIM/etc. are improved, GL
may end up giving Satlink different problems when proving the \"same\" theorem.
Since the new problems will have new checksums, the old benchmarks won't be
lost.</li>

</ul>

<p>This hook is largely implemented in Perl, so you can customize its behavior
by editing the @('books/centaur/satlink/add-benchmark.pl') script.</p>")

(defconsts *add-benchmark.pl*
  (oslib::catpath (cbd) "add-benchmark.pl"))

(define gather-benchmarks-hook ((cnf      lit-list-listp)
                                (filename stringp)
                                (status   (or (eq status :sat)
                                              (eq status :unsat)))
                                (env$)
                                (state))
  (declare (ignorable cnf filename status env$ state))
  (b* ((cmd (concatenate 'string
                         *add-benchmark.pl*
                         " --filename " filename
                         " --status " (if (eq status :sat)
                                          "sat"
                                        "unsat")
                         ;; BOZO add --comment <name of theorem>
                         ))
       ((mv ?status ?lines)
        (tshell-call cmd :print t :save nil)))
    nil))

(defattach satlink-extra-hook gather-benchmarks-hook)

#||

(tshell-ensure)

(sat '((1 2)) env$)

||#
