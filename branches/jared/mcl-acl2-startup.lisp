 Here are instructions for how to install ACL2 on MCL (Macintosh Common Lisp).
These instructions were developed for MCL 4.0 and have been used successfully
on MCL 4.2.  Thanks to Pascal Costanza for providing information pertaining to
MCL 5.0 on Mac OS X and to Warren Hunt for additional information about
linebreaks.

==================== SECTION:  Dealing with Unix linebreaks ===================

The ACL2 sources use Unix linebreaks.  MCL (at least up to and including 5.0)
expects Macintosh (classic) linebreaks.  So you need to make sure that the
linebreaks are transformed accordingly.  You can do this on the command line
with "tr" right on the uncompressed tar file, for example as follows.

  tr "\n" "\r" < acl2.tar > acl2-mac.tar

The conversion has to be made on the uncompressed "tar" file, not the ".tgz" or
".tar.gz" file.  The double quotation marks (") are important, since without
them, the "\n" and the "\r" may be interpreted by some kind of reader, e.g., a
shell, prior to being passed to "tr".

Alternatively, instead of using "tr", you can drag and drop the resulting
folder on the LineBreak utility which is available from
http://www.macalester.edu/~jaas/linebreak.html.  Or you can avoid the tar files
and fetch the files directly with appropriate linebreak handling; for example,
when Fetch determines that it is downloading ASCII text files, it automatically
converts line feeds <LF> into carriage returns <CR>, which will probably do
what is necessary.

=============================== SECTION:  Memory ==============================

ACL2 consumes quite a lot of heap space. You may want to select the MCL
application and use Command-I to set (in particular, increase) the memory.  30
or (probably) more megabytes might be a good quantity.  We invite user
suggestions for a better number, and more generally for any improvements to
this file.

MCL 5.0 uses the "classic" approach for the allocation of heap space.
You can change the memory size settings for MCL 5.0 as follows:
- Select the MCL 5.0 app.
- Press Command-I.
- Check the box "Open in the Classic environment" [sic!].
- Select the "Memory" settings and set the memory size.
- Uncheck the box "Open in the Classic environment".
- Close the Info dialog.

=========================== SECTION:  Preliminaries ===========================

The instructions below mention a certain pathname repeatedly.  The pathname as
it appears here is "xyz".  Before executing these instructions, you should
replace "xyz" by the full pathname of the ACL2 source directory, without the
final ":".  For example, "xyz" might be replaced by

  "Macintosh HD:Applications:acl2-sources"

Every occurrence of "xyz" below should be so replaced.  This also holds for
MCL 5.0 because it still expects "classic" pathnames.

Start up a Listener and execute each of the commands below.  Make sure that you
type all the commands directly in the listener, or copy and paste them from
this file.  Don't execute them from here via Command-E or the like.

===================== SECTION:  Build commands (Lisp code) ====================

; See the comments above.

(setq *default-pathname-defaults* #P"xyz:")
(ccl::set-mac-default-directory *default-pathname-defaults*)
(load "xyz:init.lsp")
(in-package "ACL2")
(check-suitability-for-acl2)

(compile-acl2)
(initialize-acl2 'include-book *acl2-pass-2-files*)

(or (not (probe-file *acl2-status-file*))
    (delete-file *acl2-status-file*))
(with-open-file (str *acl2-status-file* :direction :output)
  (format str "~s" :initialized))

; You may need to evaluate the following form if ccl::%doc-string-file
; is not already defined.  You can perhaps evaluate the MCL form
; (directory "**:mcl help") to obtain all of the MCL Help files on your
; machine and choose one that is appropriate for the MCL you are running.
; Unfortunately, you may need to do this each time you start up a saved image.
; (setq ccl::%doc-string-file "MCL Help")

; Finally, save an ACL2 application:
(cl-user::save-application "saved_acl2")

============================ SECTION:  Running ACL2 ===========================

The commands above build an ACL2 application saved_acl2 on your MacIntosh in
the acl2-sources directory where you saved it ("xyz" above).  When the
application is saved, your Lisp Listener disappears.  Now move saved_acl2 to
the directory with the MCL kernel, library and compiler files, which is
probably the directory with the MCL application that you started up in order to
build ACL2.  Alternatively, you can copy those files to the folder that
contains saved_acl2, or put aliases to them in that folder.

You can now start ACL2 by opening saved_acl2.

Now it is time to re-certify the arithmetic and meta books that come with
ACL2.  First make sure that the books subdirectory of the top-level ACL2
directory has been installed on your machine.

Start up the saved_acl2 image created above and execute:

; The following have been replaced starting with v2-6 with the set-cbd command
; below, which may suffice.
; (setq *default-pathname-defaults* "xyz:books:")
; (ccl::set-mac-default-directory *default-pathname-defaults*)
(lp)
; In the next form, XYZ is the result of replacing ":" by "/" in xyz.
(set-cbd "/XYZ/books")
(ld "certify-numbers.lisp"
    :standard-co "certify.out"
    :proofs-co "certify.proofs")

Then quit from the saved_acl2.
