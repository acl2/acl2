; I, David Rager, would like to release this under the 3-clause BSD license,
; but it currently includes some GPLv2 books.  As such, I am just distributing
; the software, without any explicit license.  Those familiar with the GPL will
; probably ascertain that this software is available to them under the GPLv2,
; but I do not explicitly license it under GPLv2.  If I ever figure out a way
; to escape the GPLv2, my plan is to try to release this file under 3-clause
; BSD (a license that is compatible with the GPLv2, whatever that means).

(in-package "ACL2")

(include-book "unicode/read-file-characters" :dir :system)
(include-book "cutil/define" :dir :system)
(local (include-book "tools/mv-nth" :dir :system))

(define read-file-characters-no-error ((filename stringp)
                                       (state state-p))
  :returns (mv (characters character-listp :hyp :fguard)
               (state state-p :hyp :fguard))
  (mv-let (data state)
    (read-file-characters filename state)
    (mv (if (stringp data)
            (prog2$ (er hard? 'read-file-characters-no-error
                        data)
                    nil)
          data)
        state)))

(defthm read-file-characters-no-error-preserves-state
  (implies (and (force (state-p1 state))
                (force (stringp filename)))
           (state-p1 (mv-nth 1 (read-file-characters-no-error filename state)))))

(defthm read-file-characters-no-error-returns-character-list
  (implies (and (force (state-p1 state))
                (force (stringp filename)))
           (character-listp (mv-nth 0 (read-file-characters-no-error filename state)))))
