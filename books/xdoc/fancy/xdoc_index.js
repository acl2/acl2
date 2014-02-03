/*
; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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
*/

"use strict";

// Public:
//
//    xindex_ready() -> Bool  -- Has the xindex been loaded and initialized?
//                               May be called at any time.
//
//    xindex_init();     -- Prepare the index for use.
//                          Must only be called after loading xindex.js
//                          Must be called before using the below functions
//
//    all_keys() -> [array of all valid keys]
//
//    uid_to_key        : UID -> KEY
//
//    topic_exists      : KEY -> bool
//    topic_uid         : KEY -> unique integer identifier
//    topic_name        : KEY -> xml encoded nice topic name
//    topic_rawname     : KEY -> non-encoded symbol-name (no package)
//    topic_short       : KEY -> xml encoded short topic description
//    topic_parent_keys : KEY -> [array of KEYS of parents]
//    topic_child_keys  : KEY -> [array of KEYS of children]
//    topic_suborder    : KEY -> [array of KEYS of children]
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

function xindex_ready()
{ return xindex_loaded; }

function all_keys()
{ return Object.keys(xhash); }

function topic_exists(key)
{ return key in xhash; }

function topic_uid(key)
{ return key in xhash ? xhash[key][0] : null; }

function topic_name(key)
{ return key in xhash ? xhash[key][1] : "Error: Key " + key + " not found"; }

function topic_rawname(key)
{ return key in xhash ? xhash[key][2] : "Error: Key " + key + " not found"; }

function topic_parent_keys(key)
{ return key in xhash ? xhash[key][4] : []; }

function topic_short(key)
{ return key in xhash ? xhash[key][5] : "Error: Key " + key + " not found"; }

function topic_child_keys(key)
{ return key in xhash ? xhash[key][6] : []; }

function topic_suborder(key)
{ return key in xhash ? xhash[key][8] : []; }

function xindex_init()
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
        var parent_keys = topic_parent_keys(child_key);
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
