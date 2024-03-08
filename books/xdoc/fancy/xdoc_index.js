/*
; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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
*/

// --------------------------------------------------------------------------
//
//                          MAIN DATA STRUCTURES
//
// --------------------------------------------------------------------------
//
// The XDOC database is split up into two files: XINDEX and XDATA.  Both of
// these files are generated ahead of time by the ACL2 code for XDOC.
//    - xindex is smaller and contains just the navigation data
//    - xdata is larger and has the full "long" strings for each topic
//
// We load these files lazily to make the page seem to appear faster!  This
// means you have to sort of be aware of when the data becomes available.  We
// load xindex first, then once it's complete we load xdata.  The formats of
// both files are described below.

// Public:
//
//    xindexReady() -> Bool  -- Has the xindex been loaded and initialized?
//                               May be called at any time.
//
//    xindexInit();     -- Prepare the index for use.
//                          Must only be called after loading xindex.js
//                          Must be called before using the below functions
//
//    allKeys() -> [array of all valid keys]
//
//    uid_to_key        : UID -> KEY
//
//    topicExists      : KEY -> bool
//    topicUid         : KEY -> unique integer identifier
//    topicName        : KEY -> xml encoded nice topic name
//    topicRawname     : KEY -> non-encoded symbol-name (no package)
//    topicShort       : KEY -> xml encoded short topic description
//    topicParentKeys : KEY -> [array of KEYS of parents]
//    topicChildKeys  : KEY -> [array of KEYS of children]
//    topicSuborder    : KEY -> [array of KEYS of children]
//
//
// Implementation details:
//
// The file xindex.js contains most of the XDOC database (the metadata like
// topic names, parents, keys---everything but the :long data).  This is a
// lot of data so we load it lazily.  Once xindex.js is loaded, we just end
// up with the "xindex" variable loaded.
//
// "xindex" contains the data in a somewhat compressed form.  To reduce its
// size, we leave out some information that we can reconstruct, e.g., the
// children of each topic.  So there's a little work we need to decode the
// xindex and turn it into a suitable table.
//
// We want to separate the format of xindex.js from the rest of the viewer
// application, and hence be able to easily change the format.
//
// The xindex holds an array of entries.  The UID for each topic is implicitly
// just its position in the array.
//
// Format of each entry (xdoc/save-fancy.lisp:json-encode-index-entry)
//
//        0     1      2         3         4
//      [key, name, rawname, parent-uids, short]
//  OR  [key, name, rawname, parent-uids, short, suborder-uids]
//
// We translate the xindex into an "xhash" of the form:
//
//             0    1      2         3          4           5       6          7             8
//    KEY -> [uid, name, rawname, parentuids, parentkeys, short, childkeys, suborder-uids, suborder-keys].

class XDocIndex {
    #xhash = new Map();

    /**
     * Load raw xindex data into this object
     * @param {Array} xindex The xindex data, of the form described in the above comment.
     */
    loadFromXindex(xindex) {
        // Fill in most of the xhash directly from the xindex
        for(const [uid, entry] of xindex.entries()) {
            const key = entry[0];
            const name = entry[1];
            const rawname = entry[2];
            const parentuids = entry[3];
            const shortstr = entry[4];
            const suborder = entry[5];
            this.#xhash.set(key, [uid,name,rawname,parentuids,[],shortstr,[],suborder,[]]);
        }

        // Fill in the parent_keys by resolving all parent uids
        const xl = xindex.length;
        for(const entry of this.#xhash.values()) {
            const parentuids = entry[3];
            for(const uid of parentuids) {
                const parentkey = (0 <= uid && uid < xl)
                                ? xindex[uid][0]
                                : "XDOC____ERROR-BROKEN-PARENT";
                entry[4].push(parentkey);
            }
        }

        // Fill in suborder_keys by resolving all suborder uids
        for(const entry of this.#xhash.values()) {
            const subuids = entry[7];
            if(subuids) {
                for(const uid of subuids) {
                    if (0 <= uid && uid < xl) {
                        const subkey = xindex[uid][0];
                        entry[8].push(subkey);
                    }
                }
            }
        }

        // Fill in all child_keys by cross-referencing parents
        for(const child_key of this.#xhash.keys()) {
            const parent_keys = this.topicParentKeys(child_key);
            for(const parent_key of parent_keys) {
                // It's incorrect, but possible for a child topic to list parents
                // that don't exist, so we have to make sure it really exists:
                if (this.topicExists(parent_key)) {
                    const parent_node = this.#xhash.get(parent_key);
                    parent_node[6].push(child_key);
                }
            }
        }
    }

    allKeys() {
        return this.#xhash.keys();
    }

    topicExists(key) {
        return this.#xhash.has(key);
    }

    getTopicField(key, field, defaultValue) {
        return this.topicExists(key) ? this.#xhash.get(key)[field] : defaultValue;
    }

    topicUid(key) {
        return this.getTopicField(key, 0, null);
    }

    topicName(key) {
        return this.getTopicField(key, 1, `Error: Key ${key} not found`);
    }

    topicRawname(key) {
        return this.getTopicField(key, 2, `Error: Key ${key} not found`);
    }

    topicParentKeys(key) {
        return this.getTopicField(key, 4, []);
    }

    topicShort(key) {
        return this.getTopicField(key, 5, `Error: Key ${key} not found`);
    }

    topicChildKeys(key) {
        return this.getTopicField(key, 6, []);
    }

    topicSuborder(key) {
        return this.getTopicField(key, 8, []);
    }
}

const XD_PNAMES = 0;
const XD_FROM = 1;
const XD_BASEPKG = 2;
const XD_LONG = 3;
const LAST_XD_IDX = XD_LONG;

// The XDATA table has the following format:
//
//   xdata:         KEY -> {"pnames"  : [array of xml encoded nice parent names],
//                          "from"    : "xml encoded string for topic location",
//                          "basepkg" : "base package name (not encoded)",
//                          "long"    : "xml encoded long topic description"}
//
// Except that we represent each entry with an array, instead of a hash, to
// save a tiny amount of space.
// An entry in this structure can be either:
// - a regular XData entry (a length-4 list)
// - a "missing topic" XData entry
// - an error XData entry
class XDocData {
    #xhash = new Map();

    loadFromXdata(xdata) {
        for(const [key, data] of Object.entries(xdata)) {
            this.add(key, data);
        }
    }

    add(key, data) {
        this.#xhash.set(key, data);
    }

    addError(key, data) {
        this.#xhash.set(key, [[], data, data, data]);
    }

    addMissing(key) {
        this.addError(key, "Error: no such topic.");
    }

    allKeys() {
        return this.#xhash.keys();
    }

    topicExists(key) {
        return this.#xhash.has(key);
    }

    getTopicField(key, field, defaultValue) {
        return this.topicExists(key) ? this.#xhash.get(key)[field] : defaultValue;
    }

    topicParentNames(key) {
        return this.getTopicField(key, XD_PNAMES, []);
    }

    topicFrom(key) {
        return this.getTopicField(key, XD_FROM, `Error: Key ${key} not found`);
    }

    topicBasepkg(key) {
        return this.getTopicField(key, XD_BASEPKG, `Error: Key ${key} not found`);
    }

    topicLong(key) {
        return this.getTopicField(key, XD_LONG, `Error: Key ${key} not found`);
    }
}
