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

var TOP_KEY = "ACL2____TOP";
var BROKEN_KEY = "ACL2____BROKEN-LINK";
var xdata_loaded = false;
var xdata = [];


// --------------------------------------------------------------------------
//
//                         RANDOM UTILITIES
//
// --------------------------------------------------------------------------


var short_plaintext_cache = {};
function topic_short_plaintext(key) {
    if (key in short_plaintext_cache) {
	return short_plaintext_cache[key];
    }
    var ret = render_text(topic_short(key));
    short_plaintext_cache[key] = ret;
    return ret;
}

function htmlEncode(value){
  // copied from stackoverflow:1219860
  return $('<div/>').text(value).html();
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
// load xindex first, then once it's complete we load xdata.  The format of
// xindex is described in xdoc_index.js.  The XDATA table is simpler:
//
//   xdata:         KEY -> {"pnames"  : [array of xml encoded nice parent names],
//                          "from"    : "xml encoded string for topic location",
//                          "basepkg" : "base package name (not encoded)",
//                          "long"    : "xml encoded long topic description"}
//
// Except that we represent each entry with an array, instead of a hash, to
// save a tiny amount of space.

var XD_PNAMES = 0;
var XD_FROM = 1;
var XD_BASEPKG = 2;
var XD_LONG = 3;

function key_title(key)
{
    return (topic_exists(key))
       ? ("XDOC &mdash; " + topic_name(key))
       : ("XDOC &mdash; " + key);
}



function apply_suborder(subkeys, keys) {
    var ret = [];
    for(var i in subkeys) {
	ret.push(subkeys[i]);
    }
    for(var i in keys) {
        var k = keys[i];
	var idx = ret.indexOf(k);
	if (idx == -1) { // new key, add it
	    ret.push(k);
	}
	// else already have it.
    }
    return ret;
}

function key_sorted_children(key) { // Returns a nicely sorted array of child_keys
    var children = topic_child_keys(key);

    var tmp = [];
    for(var i in children) {
        var child_key = children[i];
        var rawname = topic_rawname(child_key);
        tmp.push({key:child_key, rawname:rawname});
    }
    tmp.sort(function(a,b) { return alphanum(a.rawname, b.rawname); });

    var ret = [];
    for(var i in tmp) {
        ret.push(tmp[i].key);
    }

    var suborder = topic_suborder(key);
    if (suborder.length > 0) {
	return apply_suborder(suborder, ret);
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

    var name = topic_name(key);
    var tooltip = "<p>" + topic_short_plaintext(key) + "</p>";

    var node = "<ul class=\"hindex\" id=\"_nav" + id + "\">";
    node += "<li><nobr>";
    if (topic_child_keys(key).length == 0) {
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
    if (!xindex_ready()) {
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
    if (!xindex_ready()) {
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
    $("#flat").html("<p>Loading...</p>");
    nav_flat_ever_shown = true;
    setTimeout(nav_flat_really_install, 10);
}

function nav_flat_really_install() {

    var myarr = [];
    var keys = all_keys();
    for(var i in keys) {
	var key = keys[i];
        myarr.push({key:key, rawname: topic_rawname(key)});
    }
    myarr.sort(function(a,b) { return alphanum(a.rawname, b.rawname); });

    var dl = jQuery("<ul></ul>");
    var current_startchar = "";
    for(var i in myarr) {
        var key = myarr[i].key;
        var name = topic_name(key);
        var rawname = topic_rawname(key);
        var tooltip = "<p>" + topic_short_plaintext(key) + "</p>";
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
    $("#flat").html(dl);
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
    var parent_keys = topic_parent_keys(key);
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
        if (topic_exists(key)) {
            tooltip = topic_short_plaintext(pkey);
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
    var children = key_sorted_children(key);

    var dl = jQuery("<div></div>");
    for(var i in children) {
        var child_key = children[i];
        dl.append("<dt><a href=\"javascript:action_go_key('" + child_key + "')\">"
                  + topic_name(child_key)
                  + "</dt>");
        var dd = jQuery("<dd></dd>");
        dd.append(render_html(topic_short(child_key)));
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

    $(".basepkg").powerTip({placement:'sw',smartPlacement: true});
}

function dat_collapse(dat_id)
{
    $("#_dat_img" + dat_id).attr("src", "expand_subtopics.png");
    $("#_dat_ilink" + dat_id).attr("href", "JavaScript:dat_expand(" + dat_id + ")");
    $("#_dat_short" + dat_id).show();
    $("#_dat_long" + dat_id).hide();
}

var warned_about_history_state = false;

function dat_long_topic(key)
{
    // Assumes xdata[key] is ready
    var dat_id = dat_id_table.length;
    dat_id_table[dat_id] = {"key":key, "ever_expanded":false};

    var div = jQuery("<div></div>");

    var curr_state = history.state;
    if (!curr_state && !warned_about_history_state) {
	div.append(
	    "<p>Warning: your browser does not implement the history.state "
	    + "API, so your back button will lose your place.  You may wish "
	    + "to use a browser like Firefox or Chrome, instead.</p>");
	warned_about_history_state = true;
    }

    // Special handling for broken links.  We want to give XDOC manuals to have
    // customized control over the broken-link message.  For instance, the pure
    // ACL2-sources manual has a message along the lines of, "what you're looking
    // for might be in the acl2-books docs; go try the Centaur manual."  Or the
    // internal manuals within, say, Centaur, might want to say, "please report
    // this broken link to Jared."
    if (!topic_exists(key)) {
	// I think it's nice to change the title dynamically, to say what topic
	// they tried to access, instead of just generically saying Broken-Link.
        div.append("<h1>" + key + " Not Found</h1>");

	if (topic_exists(BROKEN_KEY)) {
	    div.append(render_html(xdata[BROKEN_KEY][XD_LONG]));
	}

        return div;
    }

    var from = xdata[key][XD_FROM];
    var fromp = (from == "Unknown")
                   ? "<p class='from'>Unknown Origin</p>"
                   : "<p class='from'>" + from + "</p>";

    var basepkg = htmlEncode(xdata[key][XD_BASEPKG]);
    var basediv = (basepkg == "ACL2")
                    ? ""
                    : "<div class='basepkg' data-powertip='"
                         + "<p>In links and code snippets here, symbols are "
                         + "shown relative to the <b>" + basepkg
	                 + "</b> package.</p><p>You may need <b>" + basepkg
	                 + "::</b> prefixes to call these functions, etc.</p>'>"
                         + "<b>" + basepkg + "</b><br/>Package</div>";

    var shortp;
    if (key != TOP_KEY) {
	div.append(basediv);
	div.append("<h1>" + topic_name(key) + "</h1>" + fromp);
	shortp = jQuery("<p></p>");
    } else {
	div.append("<div align=\"center\" style=\"margin-top: 1em;\"><img src='xdoc-logo.png'/></div>");
	shortp = jQuery("<p align='center'></p>");
    }

    shortp.append(render_html(topic_short(key)));
    div.append(shortp);
    div.append(render_html(xdata[key][XD_LONG]));
    if (topic_child_keys(key).length != 0) {
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

function dat_load_key(key, scroll_to)
{
    // BOZO consider doing something to find the key in the navigation
    // hierarchy somewhere, to make the navigation follow along with you?
    var keys = [key];
    //console.log("dat_load_key " + key + ", scroll to " + scroll_to);

    xdata_when_ready(keys,
    function() {
        $("#parents").html("");
        $("#data").html("");
        $("#right").scrollTop(0);
        dat_id_table = [];
        dat_load_parents(key);
        $("#data").append(dat_long_topic(key));
	$(".basepkg").powerTip({placement:'sw',smartPlacement: true});
        $("title").html(key_title(key));
	setTimeout("dat_really_scroll_to(" + scroll_to + ")", 10);
    });
}

function dat_really_scroll_to(top) {
    //console.log(" -- really scrolling to " + top);
    $("#right").scrollTop(top);
}






// --------------------------------------------------------------------------
//
//                          SEARCHING FEATURE
//
// --------------------------------------------------------------------------

var short_tokens_initialized = false;
var short_tokens = {};

function search_tokenize(plaintext) {
    var tokens = plaintext.toLowerCase().split(/[ \t\n:]+/);
    if (tokens.length == 1 && tokens[0] == "") {
	// Correct for ridiculous behavior of string.split
	return [];
    }
    for(var i in tokens) {
	var orig = tokens[i];
	var trim = orig.replace(/^[()"'`.,;?!]*/, '')
	               .replace(/[()"'`.,;?!]*$/, '');
	tokens[i] = trim;
    }
    return tokens;
}

function make_short_tokens() {
    if (short_tokens_initialized)
	return;
    var keys = all_keys();
    for(var i in keys) {
	var key = keys[i];
	var name = topic_name(key);
	var rawname = topic_rawname(key);
	var plaintext = topic_short_plaintext(key);
	var tokens = search_tokenize(name + " " + rawname + " " + plaintext);
	short_tokens[key] = tokens;
    }
    short_tokens_initialized = true;
}

function subarray_at_offsetp (a, b, n) {
    // Does array A occur at array B, starting from position N?
    var al = a.length;
    var bl = b.length - n;
    if (al > bl) {
	return false;
    }
    for(var i = 0; i < al; ++i) {
	if (a[i] != b[(i+n)])
	    return false;
    }
    return true;
}

function subarrayp (a, b) {
    var al = a.length;
    var bl = b.length;
    if (al == 0) return true;
    if (al > bl) return false;
    var stop = (bl-al)+1;
    for(var i = 0; i < stop; ++i) {
	if (subarray_at_offsetp(a,b,i))
	    return true;
    }
    return false;
}

function search_submit() {
    var str = $("#searchbox").val();
    var str_url = encodeURIComponent(str);
    var str_html = "XDOC Search &mdash; " + htmlEncode(str);
    //console.log("submitting search for " + str);
    history_save_place();
    window.history.pushState({"search":str}, str_html, "?search=" + str_url);
    search_go(str);
}

function search_go(str) {
    // Kludgy: get the page ready to receive data.
    $("#parents").html("");
    $("#parents").hide();

    $("#data").html("");
    $("#right").scrollTop(0);

    $("#data").append("<p><b style='color: red'>Note:</b> <i>search is extremely beta.</i> "
		      + "It doesn't even search the <tt>:long</tt> sections yet.</p>");

    $("#data").append("<p id='searching_message'>Searching (takes much longer the first time)...</p>");

    var query = search_tokenize(str);

    // Now wait a bit to allow that to render, before starting the search.
    setTimeout(search_go_main, 10, query);
    return false;
}

function search_add_hit(matches, hits, key) {
    if (key in matches) {
	// already showed this result, don't show it again
	return;
    }
    matches[key] = 1;
    hits.append("<dt><a href=\"javascript:action_go_key('" + key + "')\">"
		+ topic_name(key)
		+ "</a>"
//		+ " (" + topic_uid(key) + ")" // nice for debugging
		+ "</dt>");
    var dd = jQuery("<dd></dd>");
    dd.append(render_html(topic_short(key)));
    hits.append(dd);
}

function search_go_main(query) {
    make_short_tokens();

    $("#searching_message").hide();
    if (query.length == 0) {
	$("#data").append("<h3>No results (empty search)</h3>");
	return;
    }

    var query_str = query.join(" ");
    $("#data").append("<h1><u>" + htmlEncode(query_str) + "</u></h1>");

    // Matches will just bind keys we've already shown, so we don't repeatedly
    // shown a topic just because it matches multiple criteria.
    var matches = {};

    // Hits will collect all the results
    var hits = jQuery("<dl></dl>");
    var keys = all_keys();

    // We'll start with a stupid topic name search, in case there are any very
    // exact hits.
    for(var i in keys) {
	var key = keys[i];
	var name = topic_rawname(key);
	var tokens = search_tokenize(name);
	if (subarrayp(query,tokens))
	    search_add_hit(matches, hits, key);
    }

    // Next, expand to a basic topic name substring search
    for(var i in keys) {
	var key = keys[i];
	var name = topic_rawname(key);
	if (name.toLowerCase().indexOf(query_str) != -1)
	    search_add_hit(matches, hits, key);
    }

    // Next expand to a short-string search
    for(var i in keys) {
	var key = keys[i];
	var tokens = short_tokens[key];
	var uid = topic_uid(key);
	if (subarrayp(query, tokens))
	    search_add_hit(matches, hits, key);
    }

    var num_hits = Object.keys(matches).length;
    if (num_hits != 0) {
	$("#data").append("<h3><b>" + num_hits + "</b> Results</h3>");
	$("#data").append(hits);
    }
    else {
	$("#data").append("<h3>No results</h3>");
    }

    return;
}





// --------------------------------------------------------------------------
//
//                    DATA LOADING / INITIALIZATION
//
// --------------------------------------------------------------------------

$(document).ready(function()
{
    LazyLoad.js('xindex.js', onIndexLoaded);
    $(".toolbutton").powerTip({placement: 'se'});
    $(".rtoolbutton").powerTip({placement: 'sw'});
});


function jump_render(datum) {
    var key = datum["value"];
    return "<p><b class=\"sf\">" + topic_name(key) + "</b> &mdash; " +
	topic_short_plaintext(key) + "<br/><tt>" + key + "</tt></p>";
}

function jump_init() {

    var ta_data = [];
    var keys = all_keys();
    for(var i in keys) {
	var key = keys[i];
        var tokens = [];
        tokens.push(topic_rawname(key));
        var entry = {"value": key,
		     "nicename": topic_name(key),
                     "tokens": tokens};
        ta_data.push(entry);
    }

    $("#jump").typeahead([{
        name: "topics",
	local: ta_data,
	limit: 6,
	autoselect: 'first',
	template: jump_render
    }]);

    $("#jump").bind('typeahead:selected', jump_go);
    $("#jump").bind('typeahead:autocompleted', jump_go);
    $("#jumpmsg").powerTip({placement:'se'});
    $("#jump").attr("placeholder", "append");
    $("#jump").removeAttr("disabled");
}

function jump_go(obj,datum) {
    var key = datum["value"];
    if (topic_exists(key))
        action_go_key(key);
    else
        alert("Invalid key " + key);
    $("#jump").val("");
    $("#jump").typeahead('setQuery', '');
}

function search_init() {
    $("#searchbox").attr("placeholder", "files");
    $("#searchbox").removeAttr("disabled");
}





function onIndexLoaded()
{
    xindex_init();

    if (XDATAGET == "") {
        // Load xdata.js after xindex_init() because that way we know the
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
    search_init();
}

function onDataLoaded()
{
    xdata_loaded = true;
    var params = getPageParameters();

    // Make sure that BROKEN_KEY gets loaded early on, so we can always just
    // assume it is loaded.
    if (topic_exists(BROKEN_KEY)) {
	xdata_when_ready([BROKEN_KEY], function() { return; });
    }

    if ("search" in params) {
	var str = params["search"];
	var str_url = encodeURIComponent(str);
	var str_html = htmlEncode(str);
	//console.log("onDataLoaded: search for " + str + " --> 0");
	window.history.replaceState({search:str,rtop:0},
				    str_html, "?search=" + str_url);
	search_go(str);
    }

    else {
	var key = params["topic"] || TOP_KEY;
	if (!key.match(/^[A-Za-z0-9._\-]*$/)) {
	    $("#right").html("Illegal topic name, rejecting to prevent XSS attacks.");
	    return;
	}
	//console.log("onDataLoaded: key " + key + " --> 0");
	window.history.replaceState({key:key,rtop:0},
				    key_title(key), "?topic=" + key);
	dat_load_key(key, 0);
    }

    window.addEventListener('popstate',
                            function(event) {
				event.preventDefault();
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
    if (topic_exists(key)) {
        rawname = topic_rawname(key);
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

function action_go_key(key) {

    // Warning: if you change this, check for all uses of replaceState,
    // pushState, and popState, and update them to match.

    if (!xdata_loaded) {
        please_wait();
        return;
    }

    console.log("action_go_key, going to new key " + key + " --> 0");
    history_save_place();
    window.history.pushState({key:key,rtop:0}, key_title(key),
			     "?topic=" + key);
    dat_load_key(key, 0);
}

function history_save_place() {
    var curr_state = history.state;
    var rtop = $("#right").scrollTop();
    if (curr_state) {
	// Safari doesn't seem to implement history.state
	//console.log("saving place: " + curr_state.key + " --> " + rtop);
	curr_state["rtop"] = rtop;
	window.history.replaceState(curr_state, "");
    }
}

function action_go_back(data) {

    // Warning: if you change this, check for all uses of replaceState,
    // pushState, and popState, and update them to match.

    //console.log("Going back with data = " + data);

    if (!data) {
	// Browsers may do this when the page is initially loaded,
	// so ignore this event.
	// console.log("Empty data, so returning early.");
	return;
    }

    //console.log("action_go_back data: search = " + data.search
    //            + ", key = " + data.key + ", rtop = " + data.rtop);

    // I want to do something like history_save_place() here, so that
    // the forward button would also remember its place.  But that doesn't
    // worked.  All solutions to this problem look very complex, e.g.,
    // see http://stackoverflow.com/questions/14541398.  So, I give up,
    // no forward-button re-scrolling for you.

    if ("search" in data) {
	var str = data["search"];
	search_go(str);
    }

    else if ("key" in data) {
	var key = data.key;
	var rtop = ("rtop" in data) ? data["rtop"] : 0;
	if (key) {
	    dat_load_key(key, rtop);
	}
    }
}



function printer_friendly()
{
    var w = window.open("", "Printer",
			"height=600,width=640,toolbar=1,location=0,resizable=1,scrollbars=1,status=0");
    

    var html = "<html>\n"
	+ "<head>\n"
	+ "<title>Printer Friendly</title>\n"
	+ "<link rel=\"stylesheet\" type=\"text/css\" href=\"print.css\"/>"
        + "<link rel=\"shortcut icon\" href=\"favicon.png\"/>"
        + "</head><body>"
	+ $("#data").html()
	+ "</body></html>";

    w.document.write(html);

//    $(w.document.body).html(html);
 
}
