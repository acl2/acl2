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

"use strict";

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

var xindex_loaded = false;
var xhash = {};

function xindexReady()
{ return xindex_loaded; }

function allKeys()
{ return Object.keys(xhash); }

function topicExists(key)
{ return key in xhash; }

function topicUid(key)
{ return key in xhash ? xhash[key][0] : null; }

function topicName(key)
{ return key in xhash ? xhash[key][1] : "Error: Key " + key + " not found"; }

function topicRawname(key)
{ return key in xhash ? xhash[key][2] : "Error: Key " + key + " not found"; }

function topicParentKeys(key)
{ return key in xhash ? xhash[key][4] : []; }

function topicShort(key)
{ return key in xhash ? xhash[key][5] : "Error: Key " + key + " not found"; }

function topicChildKeys(key)
{ return key in xhash ? xhash[key][6] : []; }

function topicSuborder(key)
{ return key in xhash ? xhash[key][8] : []; }

function xindexInit()
{
    // Fill in most of the xhash directly from the xindex
    for(var uid in xindex) {
	var entry = xindex[uid];
	var key = entry[0];
	var name = entry[1];
	var rawname = entry[2];
	var parentuids = entry[3];
	var shortstr = entry[4];
	var suborder = entry[5];
	xhash[key] = [uid,name,rawname,parentuids,[],shortstr,[],suborder,[]];
    }

    // Fill in the parent_keys by resolving all parent uids
    var xl = xindex.length;
    for(var key in xhash) {
	var parentuids = xhash[key][3];
	for(var i in parentuids) {
	    var uid = parentuids[i];
	    var parentkey = (0 <= uid && uid < xl)
	                      ? xindex[uid][0]
	                      : "XDOC____ERROR-BROKEN-PARENT";
	    xhash[key][4].push(parentkey);
	}
    }

    // Fill in suborder_keys by resolving all suborder uids
    var xl = xindex.length;
    for(var key in xhash) {
	var subuids = xhash[key][7];
	for(var i in subuids) {
	    var uid = subuids[i];
	    if (0 <= uid && uid < xl) {
		var subkey = xindex[uid][0];
		xhash[key][8].push(subkey);
	    }
	}
    }

    // Fill in all child_keys by cross-referencing parents
    for(var child_key in xhash) {
        var parent_keys = topicParentKeys(child_key);
        for(var i in parent_keys) {
            var parent_key = parent_keys[i];
            // It's incorrect, but possible for a child topic to list parents
            // that don't exist, so we have to make sure it really exists:
            if (parent_key in xhash) {
                var parent_node = xhash[parent_key];
                parent_node[6].push(child_key);
            }
        }
    }

    xindex_loaded = true;
}
