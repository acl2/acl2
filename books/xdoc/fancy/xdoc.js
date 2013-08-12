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

var TOP_KEY = "ACL2____TOP";
var xindex_loaded = false;
var xdata_loaded = false;
var xdata = [];


// --------------------------------------------------------------------------
//
//                         RANDOM UTILITIES
//
// --------------------------------------------------------------------------

// Initialize an XSLT processor for XDOC --> HTML conversion
var xslt_processor = new XSLTProcessor();
{
    var xslt_plain = $.base64.decode(xslt_base64);
    var xslt_dom = $.parseXML(xslt_plain);
    xslt_processor.importStylesheet(xslt_dom);
}

function wrap_xdoc_fragment(str) {
    var wrap = "<!DOCTYPE xdoc [";
    wrap += "<!ENTITY mdash \"&#8212;\">";
    wrap += "<!ENTITY rarr \"&#8594;\">";
    wrap += "<!ENTITY nbsp \"&#160;\">";
    wrap += "]>";
    wrap += "<root>" + str + "</root>";
    return wrap;
}

function render_text (str) { // XDOC Markup (string) --> Plain Text Fragment
    var xml = $.parseXML(wrap_xdoc_fragment(str));
    var dom = xslt_processor.transformToFragment(xml,document);
    var str = $(dom).text();

    // It's not clear to me whether this is good or bad.  The basic problem
    // is that strings like "short" strings might legitimately have quotes
    // or apostrophes in them.  This is no problem if we're going to stick the
    // render_text into a paragraph or something like that.  But it *is* a
    // problem if we're going to stick it into an attribute like a tooltip
    // or similar.  So, just to avoid problems like that, make sure the resulting
    // string is free of " and ' characters.
    return String(str)
             .replace(/"/g, '&quot;')
             .replace(/'/g, '&apos;');
}

function render_html (str) { // XDOC Markup (string) --> HTML DOM Fragment
    var xml = $.parseXML(wrap_xdoc_fragment(str));
    var dom = xslt_processor.transformToFragment(xml,document);
    return dom;
}

function alphanum(a, b) { // Alphanumeric comparison (for nice sorting)
  // Credit: http://my.opera.com/GreyWyvern/blog/show.dml/1671288
  function chunkify(t) {
    var tz = [], x = 0, y = -1, n = 0, i, j;

    while ((i = (j = t.charAt(x++)).charCodeAt(0))) {
      var m = (i == 46 || (i >=48 && i <= 57));
      if (m !== n) {
        tz[++y] = "";
        n = m;
      }
      tz[y] += j;
    }
    return tz;
  }

  var aa = chunkify(a);
  var bb = chunkify(b);

  for (var x = 0; aa[x] && bb[x]; x++) {
    if (aa[x] !== bb[x]) {
      var c = Number(aa[x]), d = Number(bb[x]);
      if (c == aa[x] && d == bb[x]) {
        return c - d;
      } else return (aa[x] > bb[x]) ? 1 : -1;
    }
  }
  return aa.length - bb.length;
}

function starts_with_alpha(str) {
    var little_a = "a".charCodeAt(0);
    var little_z = "z".charCodeAt(0);
    var big_a = "A".charCodeAt(0);
    var big_z = "Z".charCodeAt(0);
    var code = str.charCodeAt(0);
    return (little_a <= code && code <= little_z)
        || (   big_a <= code && code <= big_z   );
}

var waitmsg = 0;
function please_wait() {
    var msgs = ["Still loading",
                "Gah, what's taking so long?",
                "Man, tubes must be clogged...",
                "The boy has no patience.",
                "It's not ready yet!",
                "Dude, stop clicking already!"];
    $("#still_loading").html("<p>" + msgs[waitmsg] + "</p>");
    $("#still_loading").fadeIn(100).delay(500).fadeOut(100);
    waitmsg = waitmsg + 1;
    if (waitmsg == msgs.length)
        waitmsg = msgs.length - 1;
}


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
// load xindex first, then once it's complete we load xdata.
//
// XINDEX is smaller.  In the xindex.js file, you can roughly think of XINDEX
// as being a mapping from:
//
//    xindex:   KEY -> { "name":"xml encoded nice topic name",
//                       "pkeys":[array of KEY for parents],
//                       "short":"xml encoded short topic description",
//                       "rawname":"non-encoded symbol-name (no package)" }
//
// Except that actually we use an array instead of a hash (which saves about
// 400 KB) from centaur/doc.lisp at the time of this writing.  The indexes
// into the array are as follows.  These MUST AGREE WITH SAVE-FANCY.LISP:

var XI_NAME    = 0;
var XI_RAWNAME = 1;
var XI_PKEYS   = 2;
var XI_SHORT   = 3;

// But once XINDEX gets loaded, we also fill in some additional information.
// In particular, it is useful to have a list of all of a topic's children.
// (This is fast and easy to construct, given that xindex already maps each
// child to its parents).  So we fill in each XINDEX entry with a "children"
// field.

var XI_CHILDREN = 4; // array of keys for children


// The XDATA table is simpler:
//
//   xdata:         KEY -> {"pnames" : [array of xml encoded nice parent names],
//                          "from"   : "xml encoded string for topic location",
//                          "long"   : "xml encoded long topic description"}
//
// Except that again we use an array to save a tiny amount of space.

var XD_PNAMES = 0;
var XD_FROM = 1;
var XD_LONG = 2;

function xindex_add_children() { // assumes xindex is populated
    for(var child_key in xindex) {
        var parent_keys = xindex[child_key][XI_PKEYS];
        for(var i in parent_keys) {
            var parent_key = parent_keys[i];
            // It's incorrect, but possible for a child topic to list parents
            // that don't exist, so we have to make sure it really exists:
            if (parent_key in xindex) {
                var parent_node = xindex[parent_key];
                if (!parent_node[XI_CHILDREN])
                    parent_node[XI_CHILDREN] = [];
                parent_node[XI_CHILDREN].push(child_key);
            }
        }
    }
    xindex_loaded = true;
}

function key_title(key)
{
    return (key in xindex)
             ? ("XDOC &mdash; " + xindex[key][XI_NAME])
             : ("XDOC &mdash; " + key);
}

function key_info(key) {
    if (key in xindex)
        return xindex[key];
    var ret = [];
    ret[XI_NAME] = "Error: Key " + key + " not found";
    ret[XI_RAWNAME] = "Error: Key " + key + " not found";
    ret[XI_PKEYS] = [];
    ret[XI_SHORT] = "Error: Key " + key + " not found";
    ret[XI_CHILDREN] = [];
    return ret;
}

function key_sorted_children(key) { // Returns a nicely sorted array of child_keys
    var info = key_info(key);
    var children = info[XI_CHILDREN];

    var tmp = [];
    for(var i in children) {
        var child_key = children[i];
        var rawname = key_info(child_key)[XI_RAWNAME];
        tmp.push({key:child_key, rawname:rawname});
    }
    tmp.sort(function(a,b) { return alphanum(a.rawname, b.rawname); });

    var ret = [];
    for(var i in tmp) {
        ret.push(tmp[i].key);
    }
    return ret;
}

function xdata_when_ready (keys, whenReady)
{
    var missing = [];  // Optimization, don't load keys we've already loaded
    for(var i in keys) {
        if (!xdata[keys[i]])
            missing.push(keys[i]);
    }

    if (missing.length == 0) {
        whenReady();
        return;
    }

    if (!XDATAGET) {
        // We're running in local mode, so we can't load any more data from
        // the server.  Any missing keys are errors!
        for(var i in missing)
            xdata[missing[i]] = "Error: no such topic.";
        whenReady();
        return;
    }

    // Else, running on a server and missing some keys.  Try to load them.
    var url = XDATAGET + "?keys=" + missing.join(":");

    $.ajax({url: url,
            type: "GET",
            dataType: "json",
            success: function(obj) {
                var results = "results" in obj && obj["results"];
                if (results && results.length == missing.length) {
                    for(var i in results)
                        xdata[missing[i]] = results[i];
                }
                else {
                    var val = "Error: malformed reply from " + url;
                    if ("error" in obj)
                        val = obj["error"];
                    for(var i in missing)
                        xdata[missing[i]] = val;
                }
                whenReady();
                return;
            },
            error: function(xhr, status, exception) {
                var val = "Error: AJAX query failed."
                        + "xhr status " + xhr.status
                        + ", text" + xhr.responseText
                        + ", exception" + exception;
                for(var i in missing)
                    xdata[missing[i]] = val;
                whenReady();
                return;
            }});
}

// // This is kind of dumb.  It would probably be much more efficient to do
// // a single query that fetches data for a list of topics.

// function xdata_when_all_ready_aux (i, keys, whenReady) {
//     if (i == keys.length) {
//      whenReady();
//      return;
//     }
//     xdata_when_ready([keys[i]],
//     function() {
//      xdata_when_all_ready_aux(1 + i, keys, whenReady);
//     });
// }

// function xdata_when_all_ready (keys, whenReady) {
//     xdata_when_all_ready_aux(0, keys, whenReady);
// }


// --------------------------------------------------------------------------
//
//                          NAVIGATION TREE
//
// --------------------------------------------------------------------------
//
// Turning the index into a navigation tree is made more complicated by the
// following mismatch.
//
//    In the xindex, each topic can have many parents.
//    In the navigation window we show a tree, i.e., there's just one parent!
//
// To reconcile this difference, we basically "replicate" topics in the tree.
// For instance, we could show the user something like this:
//
//     TOP
//      - Parent1
//          OurTopic  -------+   (occurrence 1)
//            Child1         |
//            Child2         |   The topic and its children are "replicated"
//      - Parent2            |
//          OurTopic  -------+   (occurrence 2)
//            Child1
//            Child2
//
// The tricky part is: what happens when the user clicks on Occurrence 1 of
// OurTopic?  In this case, we want to:
//
//     - hide/show the children only underneath occurrence 1, but
//     - NOT change the state of occurrence 2 or its children!
//
// This means that we need to be able to distinguish between OCCURRENCES of
// topics, not just the topic names/keys themselves.
//
// To do this, we are going to dumbly assign a "unique identifiers" to each
// node in the navigation window.
//
// To simplify some things, we insist that the TOP topic gets identifier 0.
// But otherwise, there's no reason we even need to assign these indices until
// we can see the node.  So we lazily assign IDs to other nodes, as they become
// visible in the navigation window.  These assignments are stored in the ID
// table:

var nav_id_table = []; // map of ID to {"key":KEY,"ever_expanded":bool}

function nav_make_node(key) {
    // Create the navigation entry for a new occurrence of KEY.
    var id = nav_id_table.length;
    nav_id_table[id] = {"key":key, "ever_expanded":false};

    var info = key_info(key);
    var name = info[XI_NAME];
    var tooltip = "<p>" + render_text(info[XI_SHORT]) + "</p>";

    var node = "<ul class=\"hindex\" id=\"_nav" + id + "\">";
    node += "<li><nobr>";
    if (!info[XI_CHILDREN]) {
        node += "<img src=\"leaf.png\"/>";
    }
    else {
        node += "<a id=\"_nav_ilink" + id + "\" ";
        node += " href=\"javascript:nav_expand(" + id + ")\">";
        node += "<img src=\"plus.png\" id=\"_nav_img" + id + "\"/>";
        node += "</a>";
    }
    node += "<a id=\"_golink" + id + "\" href=\"javascript:nav_go(" + id
            + ")\" data-powertip=\"" + tooltip + "\">";
    node += name;
    node += "</a>";
    node += "</nobr>";
    node += "<li><ul class=\"hindex\" id=\"_nav_tree" + id + "\"></ul></li>";
    return node;
}

function nav_activate_tooltip(id) {
    // This sort of "should" be part of nav_make_node, but it can't be because
    // the node has to be properly installed into the document before jquery
    // can find it.
    $("#_golink" + id).powerTip({placement:'se',smartPlacement: true});
}

function nav_expand(id) {
    // The user has just clicked on a node.  We may or may not have expanded it
    // already.  If we haven't expanded it before, we need to make nodes for
    // its children and add them.  If we have expanded it already, then we must
    // have subsequently collapsed it, and we just want to make it visible
    // again.
    $("#_nav_img" + id).attr("src", "minus.png");
    $("#_nav_ilink" + id).attr("href", "javascript:nav_retract(" + id + ")");
    var key = nav_id_table[id]["key"];

    if(nav_id_table[id]["ever_expanded"]) {
        $("#_nav_tree" + id).show();
        return;
    }

    nav_id_table[id]["ever_expanded"] = true;
    var info = key_info(key);
    var children = key_sorted_children(key);

    var start = nav_id_table.length; // stupid hack for tooltip activation
    var exp = "";
    for(var i in children) {
        exp += nav_make_node(children[i]);
    }
    $("#_nav_tree" + id).append(exp);

    // Activate only the tooltips that we have just added.  (If we try to
    // activate them more than once, they don't seem to work.)
    for(var i = start; i < nav_id_table.length; ++i) {
        nav_activate_tooltip(i);
    }
}

function nav_retract(id)
{
    $("#_nav_img" + id).attr("src", "plus.png");
    $("#_nav_ilink" + id).attr("href", "JavaScript:nav_expand(" + id + ")");
    $("#_nav_tree" + id).hide();
}

var nav_mode = "tree";
var nav_tree_top = 0;
var nav_flat_top = 0;
var nav_flat_ever_shown = false;

function nav_tree() {
    if (!xindex_loaded) {
        please_wait();
        return;
    }
    if (nav_mode == "tree") { return; }
    nav_flat_top = $("#left").scrollTop();
    $("#left").scrollTop(nav_tree_top);
    $("#flat").hide();
    $("#nav").show();
    nav_mode = "tree";
}

function nav_flat() {
    if (!xindex_loaded) {
        please_wait();
        return;
    }
    if (nav_mode == "flat") { return; }
    nav_tree_top = $("#left").scrollTop();
    $("#left").scrollTop(nav_flat_top);
    $("#nav").hide();
    $("#flat").show();
    nav_mode = "flat";

    if (nav_flat_ever_shown) {
       // Nothing to do, we've already built the flat index.
       return;
    }

    $("#flat").html("");

    nav_flat_ever_shown = true;

    var myarr = [];
    for(key in xindex) {
        myarr.push({key:key, rawname: xindex[key][XI_RAWNAME]});
    }
    myarr.sort(function(a,b) { return alphanum(a.rawname, b.rawname); });

    var dl = jQuery("<ul></ul>");
    var current_startchar = "";
    for(var i in myarr) {
        var key = myarr[i].key;
        var info = key_info(key);
        var name = info[XI_NAME];
        var rawname = info[XI_RAWNAME];
        var tooltip = "<p>" + render_text(info[XI_SHORT]) + "</p>";
        if ((rawname.charAt(0) != current_startchar) && starts_with_alpha(rawname)) {
            current_startchar = rawname.charAt(0).toUpperCase();
            dl.append("<li class=\"flatsec\" id=\"flat_startchar_" + current_startchar + "\"><b>"
                      + current_startchar + "</b></li>");
        }

        dl.append("<li><a class=\"flatnav\""
                  + " href=\"JavaScript:action_go_key('" + key + "')\""
                  + " data-powertip=\"" + tooltip + "\">"
                  + name
                  + "</li>");
    }
    $("#flat").append(dl);
    $(".flatnav").powerTip({placement:'se',smartPlacement: true});
}

function nav_flat_tochar(c) {
    nav_flat();
    $("#left").scrollTop(0);
    var target = $("#flat_startchar_" + c).offset().top;
    var adjust = target - $("#left").offset().top;
    $("#left").scrollTop(adjust);
}

function nav_go(id)
{
    var key = nav_id_table[id]["key"];
    action_go_key(key);
}



// --------------------------------------------------------------------------
//
//                          MAIN DATA DISPLAY
//
// --------------------------------------------------------------------------
//
// My first cut at the data display didn't have any way to expand subtopics,
// and that was nice and simple.  But subtopic expansion seems like a cool
// feature.  To support it recursively, we run into the same multi-parent
// problem as above in the hierarchical navigation tree.  The same solution
// works again.  But this time we need to clear the ID table every time we
// go to a new topic.

var dat_id_table = []; // map of Occurrence ID to {"key":KEY,"ever_expanded":bool}

function dat_load_parents(key) {
    // Assumes xdata[key] is ready
    var info = key_info(key);
    var parent_keys = info[XI_PKEYS];
    var parent_names = xdata[key][XD_PNAMES];
    var acc = "";
    if (parent_keys.length == 0) {
        $("#parents").hide();
        $("#parents").html("");
        return;
    }
    acc += "<ul>";
    for(var i in parent_keys) {
        var pkey = parent_keys[i];
        var pname = parent_names[i];
        var tooltip = "Error: parent topic is missing!";
        if (pkey in xindex) {
            var pinfo = xindex[pkey];
            tooltip = render_text(pinfo[XI_SHORT]);
        }
        acc += "<li>";
        acc += "<a href=\"javascript:action_go_key('" + pkey + "')\""
            + "data-powertip=\"<p>" + tooltip + "</p>\">";
        acc += pname;
        acc += "</a>";
        acc += "</li>\n";
    }
    acc += "</ul>";
    $("#parents").html(acc);
    $("#parents a").powerTip({placement:'se',smartPlacement: true});
    $("#parents").show();
}

function dat_short_subtopics(key)
{
    var info = key_info(key);
    var children = key_sorted_children(key);

    var dl = jQuery("<div></div>");
    for(var i in children) {
        var child_key = children[i];
        var child_info = key_info(child_key);
        dl.append("<dt><a href=\"javascript:action_go_key('" + child_key + "')\">"
                  + child_info[XI_NAME]
                  + "</dt>");
        var dd = jQuery("<dd></dd>");
        dd.append(render_html(child_info[XI_SHORT]));
        dl.append(dd);
    }
    return dl;
}

function dat_expand(dat_id)
{
    $("#_dat_img" + dat_id).attr("src", "collapse_subtopics.png");
    $("#_dat_ilink" + dat_id).attr("href", "JavaScript:dat_collapse(" + dat_id + ")");
    $("#_dat_short" + dat_id).hide();
    $("#_dat_long" + dat_id).show();

    if (dat_id_table[dat_id]["ever_expanded"] == true) {
        // Already showed it, nothing more to do
        return;
    }

    dat_id_table[dat_id]["ever_expanded"] = true;
    var key = dat_id_table[dat_id]["key"];
    var info = key_info(key);
    var children = key_sorted_children(key);
    xdata_when_ready(children,
    function(){
        var div = $("#_dat_long" + dat_id);
        for(var i in children) {
            var child_key = children[i];
            div.append(dat_long_topic(child_key));
            if (i != children.length - 1) {
                div.append("<hr></hr>");
            }
        }
    });
}

function dat_collapse(dat_id)
{
    $("#_dat_img" + dat_id).attr("src", "expand_subtopics.png");
    $("#_dat_ilink" + dat_id).attr("href", "JavaScript:dat_expand(" + dat_id + ")");
    $("#_dat_short" + dat_id).show();
    $("#_dat_long" + dat_id).hide();
}

function dat_long_topic(key)
{
    // Assumes xdata[key] is ready
    var dat_id = dat_id_table.length;
    dat_id_table[dat_id] = {"key":key, "ever_expanded":false};

    var div = jQuery("<div></div>");
    if (!(key in xindex)) {
        div.append("<h3>Error: " + key + " not found</h3>");
        return div;
    }

    var info = xindex[key];
    var from = xdata[key][XD_FROM];
    var fromp = (from == "Unknown")
                   ? ""
                   : "<p class='from'>" + xdata[key][XD_FROM] + "</p>";
    var shortp;
    if (key != TOP_KEY) {
	div.append("<h1>" + info[XI_NAME] + "</h1>" + fromp);
	shortp = jQuery("<p></p>");
    } else {
	div.append("<h1><img src='xdoc-logo.png'/></h1>");
	shortp = jQuery("<p align='center'></p>");
    }
    shortp.append(render_html(info[XI_SHORT]));
    div.append(shortp);
    div.append(render_html(xdata[key][XD_LONG]));
    if (info[XI_CHILDREN]) {
        var acc = "<h3>";
        acc += "Subtopics ";
        acc += "<a id=\"_dat_ilink" + dat_id + "\""
                + " href=\"javascript:dat_expand(" + dat_id + ")\">";
        acc += "<img id=\"_dat_img" + dat_id + "\""
                + " src=\"expand_subtopics.png\" align=\"top\"/>";
        acc += "</a>";
        acc += "</h3>";
        var sub = jQuery("<dl id=\"_dat_short" + dat_id + "\"></dl>");
        sub.append(dat_short_subtopics(key));
        div.append(acc);
        div.append(sub);
        div.append("<div id=\"_dat_long" + dat_id + "\" "
                   + "style=\"display:none\" class=\"dat_long\"></dl>");
    }

    return div;
}

function dat_load_key(key)
{
    // BOZO consider doing something to find the key in the navigation
    // hierarchy somewhere, to make the navigation follow along with you?
    var keys = [key];
    xdata_when_ready(keys,
    function() {
        $("#parents").html("");
        $("#data").html("");
        $("#right").scrollTop(0);
        dat_id_table = [];
        dat_load_parents(key);
        $("#data").append(dat_long_topic(key));
        $("title").html(key_title(key));
    });
}




// --------------------------------------------------------------------------
//
//                    DATA LOADING / INITIALIZATION
//
// --------------------------------------------------------------------------

$(document).ready(function()
{
    LazyLoad.js('xindex.js', onIndexLoaded);
    $(".toolbutton").powerTip({placement:'se'});
});


function jump_init() {

    var ta_data = [];
    for(var key in xindex) {
        var info = xindex[key];
        var tokens = [];
        tokens.push(info[XI_RAWNAME]);
        var entry = {"value": key,
                     "nicename": info[XI_NAME],
                     "short": render_text(info[XI_SHORT]),
                     "tokens": tokens};
        ta_data.push(entry);
    }

    $("#jump").typeahead([{
            name: "topics",
            local: ta_data,
            limit: 6,
            template: "<p><b class=\"sf\">{{{nicename}}}</b> &mdash; {{{short}}}<br/>"
                     + "<tt>{{value}}</tt></p>",
            engine: Hogan
    }]);

    $("#jump").bind('typeahead:selected', jump_go);
    $("#jump").bind('typeahead:autocompleted', jump_go);
    $("#jumpmsg").powerTip({placement:'se'});
    $("#jump").attr("placeholder", "append");
    $("#jump").removeAttr("disabled");
}

function jump_go(obj,datum) {
    var key = datum["value"];
    if (key in xindex)
        action_go_key(key);
    else
        alert("Invalid key " + key);
    $("#jump").val("");
    $("#jump").typeahead('setQuery', '');
}


function onIndexLoaded()
{
    xindex_add_children();

    if (XDATAGET == "") {
        // Load xdata.js after xindex_add_children because that way we know the
        // index is fully initialized by the time we run onDataLoaded.
        LazyLoad.js('xdata.js', onDataLoaded);
    }
    else {
        // Running with the support of a server.  We can just regard the data
        // as already loaded.
        onDataLoaded();
    }

    var acc = "";
    var chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    for(var i in chars) {
        var c = chars.charAt(i);
        acc += "<a href=\"javascript:nav_flat_tochar('" + c + "')\">" + c + "</a>";
        if (c == "M")
            acc += "<br/>";
    }
    $("#letters").html(acc);

    var top_node = nav_make_node(TOP_KEY);
    $("#nav").html(top_node);
    nav_expand(0);
    nav_activate_tooltip(0);

    jump_init();
}

function onDataLoaded()
{
    xdata_loaded = true;
    var params = getPageParameters();
    var key = params["topic"] || TOP_KEY;
    if (!key.match(/^[A-Za-z0-9._\-]*$/)) {
        $("#right").html("Illegal topic name, rejecting to prevent XSS attacks.");
        return;
    }

    window.history.replaceState({"key":key}, key_title(key), "?topic=" + key);
    dat_load_key(key);

    window.addEventListener('popstate',
                            function(event) {
                                action_go_back(event.state);
                            });
}

function getPageParameters ()
{
   var ret = {};
   if (!window.location.toString().match(/\?(.+)$/)) {
       return ret;
   }
   var param_strs = RegExp.$1.split("&");
   var param_arr = {};
   for(var i in param_strs)
   {
      var tmp = param_strs[i].split("=");
      var key = decodeURI(tmp[0]);
      var val = decodeURI(tmp[1]);
      param_arr[key] = val;
   }
   return param_arr;
}


function srclink(key)
{
    // BOZO stupid hack, eventually generate this without the .xdoc-link part.
    key = key.replace(".xdoc-link", "");
    var rawname = key;
    if (key in xindex) {
        rawname = xindex[key][XI_RAWNAME];
    }

    // Fancy Data URL generator
    var srclink_header =
        "; -*- mode: xdoc-link -*-\n" +
        "; This is an XDOC Link file.\n" +
        "; Ordinarily, you should not see this file.\n" +
        ";\n" +
        "; If you are viewing this file in a web browser, you probably\n" +
        "; have not configured your web browser to send .xdoc-link files\n" +
        "; to Emacs.\n" +
        ";\n" +
        "; If you are viewing this file in Emacs, you probably have not\n" +
        "; loaded xdoc.el from the xdoc/ directory.\n" +
        ";\n" +
        "; For more information, please see \"Emacs Links\" in the XDOC\n" +
        "; manual.\n\n"

    window.open('data:application/x-acl2-xdoc-link;charset=utf-8,' +
    encodeURIComponent(srclink_header + rawname));
}

function action_go_key(key)
{
    if (!xdata_loaded) {
        please_wait();
        return;
    }
    window.history.pushState({"key":key}, key_title(key), "?topic=" + key);
    dat_load_key(key);
}

function action_go_back(data) {
    var key = ("key" in data) ? data["key"] : null;
    if (key) {
        dat_load_key(key);
    }
}



