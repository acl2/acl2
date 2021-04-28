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
function topicShortPlaintext(key) {
    if (key in short_plaintext_cache) {
	return short_plaintext_cache[key];
    }
    var ret = renderText(topicShort(key));
    short_plaintext_cache[key] = ret;
    return ret;
}

function htmlEncode(value){
  // copied from stackoverflow:1219860
  return $('<div/>').text(value).html();
}

// Alphanumeric comparison (for nice sorting), adapted from
//    http://my.opera.com/GreyWyvern/blog/show.dml/1671288

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

function alphanumChunks(aa,bb) {
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

function alphanum(a, b) {
  var aa = chunkify(a);
  var bb = chunkify(b);
  return alphanumChunks(aa,bb);
}

var waitmsg = 0;
function pleaseWait() {
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


var KATEX_LOADED = 0;

function onKatexLoaded()
{
    KATEX_LOADED = 1;
    renderMathFragments();
}

function renderMathFragments ()
{
    // Need to call this whenever we potentially add new .mathfrag divs into
    // the page.

    if (! KATEX_LOADED) {
	// just wait, it'll get loaded eventually
	return;
    }

    // console.log("Rendering math fragments.");
    $(".mathblock").each(function () {
        var obj = $(this);
    	var formula_text = obj.text();
        var newdiv = jQuery("<span></span>");
	try {
	    katex.render(formula_text, newdiv.get(0));
    	    obj.html(newdiv);
	    obj.removeAttr("class");
	    obj.attr("class", "mathblockrendered");
	}
	catch(e) {
	    obj.html(htmlEncode("{{" + e.message + "}}"));
	}
    });

    $(".mathfrag").each(function () {
        var obj = $(this);
    	var formula_text = obj.text();
        var newdiv = jQuery("<span></span>");
	try {
	    katex.render(formula_text, newdiv.get(0));
	    obj.html(newdiv);
	    obj.removeAttr("class");
	    obj.attr("class", "mathfragrendered");
    	}
	catch (e) {
	    obj.html(htmlEncode("{{" + e.message + "}}"));
	}
    });
}

function maybePowertip(selector, options)
{
    // Gross hack follows.  Sorry.
    //
    // I've used PowerTip since the first version of the fancy viewer and it
    // works great for Desktop browsers.  However, for mobile it seems buggy.
    // In particular, even though you are touching the screen and have no
    // mouse, the powertip would still get activated when you would touch the
    // menu button.  Worse, it wouldn't go away(!) and just sat there blocking
    // the menu.
    //
    // So awful workaround: I now use this stupid wrapper instead of directly
    // activating .powerTip() -- this lets me track every powertip'able element
    // has the horrible-powertip-tracker class.  This allows me to write
    // closeAllPowertips to close all possible powertips.
    //
    // Sprinkling calls of closeAllPowertips() throughout the code then
    // suffices to make sure that, e.g., toggling the navigation menu doesn't
    // leave you with powertips hanging around.

    $(selector).powerTip(options);
    $(selector).addClass("horrible-powertip-tracker");
}

function closeAllPowertips()
{
//    console.log("CloseAllPowertips Enters");
    $(".horrible-powertip-tracker").powerTip('hide');
//    console.log("CloseAllPowertips Exits");
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

function keyTitle(key)
{
    var prefix = XDOCTITLE;
    if (!prefix) { prefix = "XDOC"; }

    return (topicExists(key))
       ? (prefix + " &mdash; " + topicName(key))
       : (prefix + " &mdash; " + key);
}



function applySuborder(subkeys, keys) {
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

function keySortedChildren(key) { // Returns a nicely sorted array of child_keys
    var children = topicChildKeys(key);

    var tmp = [];
    for(var i in children) {
        var child_key = children[i];
        var rawname = topicRawname(child_key);
        tmp.push({key:child_key, rawname:rawname});
    }
    tmp.sort(function(a,b) { return alphanum(a.rawname, b.rawname); });

    var ret = [];
    for(var i in tmp) {
        ret.push(tmp[i].key);
    }

    var suborder = topicSuborder(key);
    if (suborder.length > 0) {
	return applySuborder(suborder, ret);
    }

    return ret;
}

function xdataWhenReady (keys, whenReady)
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

function navMakeNode(key) {
    // Create the navigation entry for a new occurrence of KEY.
    var id = nav_id_table.length;
    nav_id_table[id] = {"key":key, "ever_expanded":false};

    var name = topicName(key);
    var tooltip = "<p>" + topicShortPlaintext(key) + "</p>";

    var node = "<ul class=\"hindex\" id=\"_nav" + id + "\">";
    node += "<li><nobr>";
    if (topicChildKeys(key).length == 0) {
        node += "<img src=\"leaf.png\"/>";
    }
    else {
        node += "<a id=\"_nav_ilink" + id + "\" ";
        node += " href=\"javascript:navExpand(" + id + ")\">";
        node += "<img src=\"plus.png\" id=\"_nav_img" + id + "\"/>";
        node += "</a>";
    }
    node += "<a id=\"_golink" + id + "\""
	  + " href=\"index.html?topic=" + key + "\""
          + " onclick=\"return dolink(event, '" + key + "');\""
          + " data-powertip=\"" + tooltip + "\">";
    node += name;
    node += "</a>";
    node += "</nobr>";
    node += "<li><ul class=\"hindex\" id=\"_navTree" + id + "\"></ul></li>";
    return node;
}

function navActivateTooltip(id) {
    // This sort of "should" be part of navMakeNode, but it can't be because
    // the node has to be properly installed into the document before jquery
    // can find it.
    maybePowertip("#_golink" + id, {placement:'se',smartPlacement: true});
}

function navExpand(id) {
    // The user has just clicked on a node.  We may or may not have expanded it
    // already.  If we haven't expanded it before, we need to make nodes for
    // its children and add them.  If we have expanded it already, then we must
    // have subsequently collapsed it, and we just want to make it visible
    // again.
    $("#_nav_img" + id).attr("src", "minus.png");
    $("#_nav_ilink" + id).attr("href", "javascript:navRetract(" + id + ")");
    var key = nav_id_table[id]["key"];

    if(nav_id_table[id]["ever_expanded"]) {
        $("#_navTree" + id).show();
        return;
    }

    nav_id_table[id]["ever_expanded"] = true;
    var children = keySortedChildren(key);

    var start = nav_id_table.length; // stupid hack for tooltip activation
    var exp = "";
    for(var i in children) {
        exp += navMakeNode(children[i]);
    }
    $("#_navTree" + id).append(exp);

    // Activate only the tooltips that we have just added.  (If we try to
    // activate them more than once, they don't seem to work.)
    for(var i = start; i < nav_id_table.length; ++i) {
        navActivateTooltip(i);
    }
}

function navRetract(id)
{
    $("#_nav_img" + id).attr("src", "plus.png");
    $("#_nav_ilink" + id).attr("href", "JavaScript:navExpand(" + id + ")");
    $("#_navTree" + id).hide();
}

var nav_mode = "tree";
var navTree_top = 0;
var navFlat_top = 0;
var navFlat_ever_shown = false;

function navTree() {
    if (!xindexReady()) {
        pleaseWait();
        return;
    }
    if (nav_mode == "tree") { return; }
    navFlat_top = $("#left").scrollTop();
    $("#left").scrollTop(navTree_top);
    $("#flat").hide();
    $("#nav").show();
    closeAllPowertips();
    nav_mode = "tree";
}

function navFlat() {
    if (!xindexReady()) {
        pleaseWait();
        return;
    }
    if (nav_mode == "flat") { return; }
    navTree_top = $("#left").scrollTop();
    $("#left").scrollTop(navFlat_top);
    $("#nav").hide();
    $("#flat").show();
    closeAllPowertips();
    nav_mode = "flat";

    if (navFlat_ever_shown) {
       // Nothing to do, we've already built the flat index.
       return;
    }
    $("#flat").html("<p>Loading...</p>");
    navFlat_ever_shown = true;
    setTimeout(navFlatReallyInstall, 10);
}


function navFlatSort(array)
{
    var len = array.length;
    if(len < 2) {
	return array;
    }
    var pivot = Math.ceil(len/2);
    return navFlatMerge(navFlatSort(array.slice(0,pivot)), navFlatSort(array.slice(pivot)));
}

function navFlatMerge(left, right)
{
    var result = [];
    while((left.length > 0) && (right.length > 0))
    {
	if (alphanumChunks(left[0].chunks, right[0].chunks) == -1)
	    result.push(left.shift());
	else
	    result.push(right.shift());
    }

    result = result.concat(left, right);
    return result;
};

function navFlatReallyInstall()
{
// On the combined ACL2+Books manual circa May 2016, this had gotten unusably
// slow (175s).  The main culprits seemed to be:
//
//   - Sorting the topic names was unnecessarily and incredibly slow.  The
//     alphanum function was chunkifying its arguments each time it was called.
//     We can do a lot better by (linearly) chunkifying everything first before
//     sorting, and then just sorting the chunks.
//
//   - Building tooltips for every single topic was slow.  Just calling
//     topicShortPlaintext(key) for each key seemed to take around 14 seconds.
//     It seems difficult to reduce this expense.  For now I think the most
//     reasonable thing to do is just abandon these tooltips as too slow :(
//
//   - Building the <ul>...</ul> with jquery was slow.  Switching to just use
//     string concatenation seems to help a lot.
//
// The above changes got the flat index down to about 6 seconds without
// sorting, but sorting the array with the nice:
//
//     myarr.sort(function(a,b) {
//         return alphanumChunks(a.chunks, b.chunks);
//     });
//
// was bringing the time up to 20 seconds in Firefox's profile, or about 6
// seconds of walltime as I actually count along without profiling enabled.
// Using the above mergesort instead reduced the time down to 14 seconds in the
// profile, which translates into about 3 seconds of walltime as I actually
// count it.  So that's pretty great.  Probably the above sort isn't ideal; I
// haven't tried out others yet.  But this is probably getting fast enough.

    var big_a = "A".charCodeAt(0);
    var big_z = "Z".charCodeAt(0);

    var myarr = [];
    var keys = allKeys();

    // Preprocessing: upcase and chunkify everything
    for(var i in keys) {
	var key = keys[i];
	var rawname = topicRawname(key).toUpperCase();
        myarr.push({key:key, rawname: rawname, chunks: chunkify(rawname) });
    }

    // Sort using faster algorithm
    myarr = navFlatSort(myarr);
    // myarr.sort(function(a,b) {
    // 	return alphanumChunks(a.chunks, b.chunks);
    // });

    // Previously used jQuery("<ul></ul>") and extended it with append.  That
    // was much slower -- switching to string appends cut off 2.3 seconds from
    // a small manual.
    var dl = "<ul>";
    var current_startchar = "";

    // Previously we used a separate function to test if things started with
    // alphabetic characters.  Now we inline this to gain some small
    // efficiency.

    for(var i in myarr) {
        var key = myarr[i].key;
        var name = topicName(key);
        var rawname = myarr[i].rawname;

	// If you want to resurrect this, also need to add the data-powertip
	// stuff into the link.  var tooltip = "<p>" + topicShortPlaintext(key)
	// + "</p>";

	var code = rawname.charCodeAt(0);
        if ((rawname.charAt(0) != current_startchar) &&
	    // Avoid headers unless it's alphabetic.  Only need to check for
	    // upper-case things since we're upcasing everything to begin with.
	    ((big_a <= code && code <= big_z)))
	{
            current_startchar = rawname.charAt(0);
	    dl += "<li class=\"flatsec\" id=\"flat_startchar_" + current_startchar + "\"><b>"
                      + current_startchar + "</b></li>";
        }

        dl += "<li><a class=\"flatnav\""
                  + " href=\"index.html?topic=" + key + "\""
                  + " onclick=\"return dolink(event, '" + key + "');\">"
                  + name
                  + "</a></li>";
    }
    dl += "</ul>";
    $("#flat").html(dl);

    // If we ever restore tooltips...
    //    maybePowertip(".flatnav", {placement:'se',smartPlacement: true});
}


function navFlatToChar(c) {
    navFlat();
    $("#left").scrollTop(0);
    var target = $("#flat_startchar_" + c).offset().top;
    var adjust = target - $("#left").offset().top;
    $("#left").scrollTop(adjust);
}

function navGo(id)
{
    var key = nav_id_table[id]["key"];
    actionGoKey(key);
}

function navToggleVisible()
{
    // Small displays (mobile) only -- we hide the navigation until the menu
    // button is pressed.

    $("#left").toggleClass("active");
    closeAllPowertips();
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

function datLoadParents(key) {
    // Assumes xdata[key] is ready
    var parent_keys = topicParentKeys(key);
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
        if (topicExists(key)) {
            tooltip = topicShortPlaintext(pkey);
        }
        acc += "<li>";
        acc += "<a href=\"index.html?topic=" + pkey + "\""
	    + " onclick=\"return dolink(event, '" + pkey + "');\""
            + " data-powertip=\"<p>" + tooltip + "</p>\">";
        acc += pname;
        acc += "</a>";
        acc += "</li>\n";
    }
    acc += "</ul>";
    $("#parents").html(acc);
    maybePowertip("#parents a", {placement:'se',smartPlacement: true});
    $("#parents").show();
}

function datShortSubtopics(key)
{
    var children = keySortedChildren(key);

    var dl = jQuery("<div></div>");
    for(var i in children) {
        var child_key = children[i];
        dl.append("<dt><a href=\"index.html?topic=" + child_key + "\""
                  + " onclick=\"return dolink(event, '" + child_key + "');\""
		  + ">"
                  + topicName(child_key)
                  + "</dt>");
        var dd = jQuery("<dd></dd>");
        dd.append(renderHtml(topicShort(child_key)));
        dl.append(dd);
    }
    return dl;
}

function datExpand(dat_id)
{
    $("#_dat_img" + dat_id).attr("src", "collapse_subtopics.png");
    $("#_dat_ilink" + dat_id).attr("href", "JavaScript:datCollapse(" + dat_id + ")");
    $("#_dat_short" + dat_id).hide();
    $("#_dat_long" + dat_id).show();

    if (dat_id_table[dat_id]["ever_expanded"] == true) {
        // Already showed it, nothing more to do
        return;
    }

    dat_id_table[dat_id]["ever_expanded"] = true;
    var key = dat_id_table[dat_id]["key"];
    var children = keySortedChildren(key);
    xdataWhenReady(children,
    function(){
        var div = $("#_dat_long" + dat_id);
        for(var i in children) {
            var child_key = children[i];
            div.append(datLongTopic(child_key));
            if (i != children.length - 1) {
                div.append("<hr></hr>");
            }
        }
    });

    maybePowertip(".basepkg", {placement:'sw',smartPlacement: true});
    renderMathFragments();
}

function datCollapse(dat_id)
{
    $("#_dat_img" + dat_id).attr("src", "expand_subtopics.png");
    $("#_dat_ilink" + dat_id).attr("href", "JavaScript:datExpand(" + dat_id + ")");
    $("#_dat_short" + dat_id).show();
    $("#_dat_long" + dat_id).hide();
}

var warned_about_history_state = false;

function datLongTopic(key)
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
    if (!topicExists(key)) {
	// I think it's nice to change the title dynamically, to say what topic
	// they tried to access, instead of just generically saying Broken-Link.
        div.append("<h1>" + key + " Not Found</h1>");

	if (topicExists(BROKEN_KEY)) {
	    div.append(renderHtml(xdata[BROKEN_KEY][XD_LONG]));
	}

        return div;
    }

    var from = xdata[key][XD_FROM];
    var fromp;
    if (from == "Unknown") {
        fromp = "<p class='from'>Unknown Origin</p>";
    }
    else if (from == "ACL2 Sources") {
        // link to main ACL2 sources dir:
        fromp = "<p class='from'><a href=\"https://github.com/acl2/acl2\">ACL2 Sources</a></p>";
    }
    else if (from.startsWith("[books]")) {
        // link to the specific file on GitHub:
        fromp = "<p class='from'><a href=\"https://github.com/acl2/acl2/tree/master/books"
            + from.substring(7) // strip "[books]" from front
            + "\">" + from + "</a></p>";
    }
    else {
        fromp = "<p class='from'>" + from + "</p>";
    }

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
	div.append("<h1>" + topicName(key) + "</h1>" + fromp);
	shortp = jQuery("<p></p>");
    } else {
	div.append("<div align=\"center\" style=\"margin-top: 1em;\"><img src='xdoc-logo.png'/></div>");
	shortp = jQuery("<p align='center'></p>");
    }

    shortp.append(renderHtml(topicShort(key)));
    div.append(shortp);
    div.append(renderHtml(xdata[key][XD_LONG]));
    if (topicChildKeys(key).length != 0) {
        var acc = "<h3>";
        acc += "Subtopics ";
        acc += "<a id=\"_dat_ilink" + dat_id + "\""
                + " href=\"javascript:datExpand(" + dat_id + ")\">";
        acc += "<img id=\"_dat_img" + dat_id + "\""
                + " src=\"expand_subtopics.png\" align=\"top\"/>";
        acc += "</a>";
        acc += "</h3>";
        var sub = jQuery("<dl id=\"_dat_short" + dat_id + "\"></dl>");
        sub.append(datShortSubtopics(key));
        div.append(acc);
        div.append(sub);
        div.append("<div id=\"_dat_long" + dat_id + "\" "
                   + "style=\"display:none\" class=\"dat_long\"></dl>");
    }

    return div;
}

function datLoadKey(key, scroll_to)
{
    // BOZO consider doing something to find the key in the navigation
    // hierarchy somewhere, to make the navigation follow along with you?
    var keys = [key];

    xdataWhenReady(keys,
    function() {
        $("#parents").html("");
        $("#data").html("");
        $("#right").scrollTop(0);
        dat_id_table = [];
        datLoadParents(key);
        $("#data").append(datLongTopic(key));
	maybePowertip(".basepkg", {placement:'sw',smartPlacement: true});
        $("title").html(keyTitle(key));
	renderMathFragments();
	setTimeout("datReallyScrollTo(" + scroll_to + ")", 10);
    });
}

function datReallyScrollTo(top) {
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

function searchTokenize(plaintext) {
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

function makeShortTokens() {
    if (short_tokens_initialized)
	return;
    var keys = allKeys();
    for(var i in keys) {
	var key = keys[i];
	var name = topicName(key);
	var rawname = topicRawname(key);
	var plaintext = topicShortPlaintext(key);
	var tokens = searchTokenize(name + " " + rawname + " " + plaintext);
	short_tokens[key] = tokens;
    }
    short_tokens_initialized = true;
}

function subarrayAtOffsetp (a, b, n) {
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
	if (subarrayAtOffsetp(a,b,i))
	    return true;
    }
    return false;
}

function searchSubmit() {
    var str = $("#searchbox").val();
    var str_url = encodeURIComponent(str);
    var str_html = "XDOC Search &mdash; " + htmlEncode(str);
    //console.log("submitting search for " + str);
    historySavePlace();
    window.history.pushState({"search":str}, str_html, "?search=" + str_url);
    searchGo(str);
}

function searchGo(str) {
    // Kludgy: get the page ready to receive data.
    $("#parents").html("");
    $("#parents").hide();

    $("#data").html("");
    $("#right").scrollTop(0);

    $("#data").append("<p><b style='color: red'>Note:</b> <i>search is extremely beta.</i> "
		      + "It doesn't even search the <tt>:long</tt> sections yet.</p>");

    $("#data").append("<p id='searching_message'>Searching (takes much longer the first time)...</p>");

    var query = searchTokenize(str);

    // if we're in mobile mode, hide the navigation bar whenever the
    // user navigates to a new page.
    $("#left").removeClass("active");
    closeAllPowertips();

    // Now wait a bit to allow that to render, before starting the search.
    setTimeout(searchGoMain, 10, query);
    return false;
}

function searchAddHit(matches, hits, key) {
    if (key in matches) {
	// already showed this result, don't show it again
	return;
    }
    matches[key] = 1;
    hits.append("<dt><a href=\"index.html?topic=" + key + "\""
		+ " onclick=\"return dolink(event, '" + key + "');\">"
		+ topicName(key)
		+ "</a>"
//		+ " (" + topicUid(key) + ")" // nice for debugging
		+ "</dt>");
    var dd = jQuery("<dd></dd>");
    dd.append(renderHtml(topicShort(key)));
    hits.append(dd);
}

function searchGoMain(query) {
    makeShortTokens();

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
    var keys = allKeys();

    // We'll start with a stupid topic name search, in case there are any very
    // exact hits.
    for(var i in keys) {
	var key = keys[i];
	var name = topicRawname(key);
	var tokens = searchTokenize(name);
	if (subarrayp(query,tokens))
	    searchAddHit(matches, hits, key);
    }

    // Next, expand to a basic topic name substring search
    for(var i in keys) {
	var key = keys[i];
	var name = topicRawname(key);
	if (name.toLowerCase().indexOf(query_str) != -1)
	    searchAddHit(matches, hits, key);
    }

    // Next expand to a short-string search
    for(var i in keys) {
	var key = keys[i];
	var tokens = short_tokens[key];
	var uid = topicUid(key);
	if (subarrayp(query, tokens))
	    searchAddHit(matches, hits, key);
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
    maybePowertip(".toolbutton", {placement: 'se'});
    maybePowertip(".rtoolbutton", {placement: 'sw'});
});


function jumpRender(datum) {
    var key = datum["value"];
    var ret = "";
    ret += "<p>";
//    ret += topicUid(key) + " &mdash; "; // nice for debugging
    ret += "<b class=\"sf\">" + topicName(key) + "</b>";
    var shortmsg = topicShortPlaintext(key);
    if (shortmsg != "") {
	ret += " &mdash; " + shortmsg;
    }
    ret += "<br/><tt>" + key + "</tt></p>";
    return ret;
}

function jumpInit() {

    var ta_data = [];
    var keys = allKeys();
    for(var i in keys) {
	var key = keys[i];
        var tokens = [];
        tokens.push(topicRawname(key));
        var entry = {"value": key,
		     "nicename": topicName(key),
                     "tokens": tokens,
		     // We precompute these for faster sorting:
		     "nicelow": topicName(key).toLowerCase(),
		     "uid": topicUid(key),
		     };
        ta_data.push(entry);
    }

    var engine1 = new Bloodhound({
	name: 'topics',
	local: ta_data,
	limit: 20,
	datumTokenizer: function(data) {
	    return data.tokens;
	},
	queryTokenizer: Bloodhound.tokenizers.whitespace
    });

    // Bloodhound natively lets you supply a sort function that just
    // compares two elements.  However, that turned out to be too
    // slow.  By using our own sorting function we can
    //
    //  (1) avoid having to look at the current typeahead value on
    //      every single comparison, which was very slow when doing lots of
    //      comparisons.
    //
    //  (2) pre-filter the array to make this mostly linear.
    engine1.sorter = function(matches)
    {
	//console.log("My sorter called on " + matches.length + " elements.");
	var curr = $("#jump").typeahead('val').toLowerCase();

	var compare = function(a,b)
	{
	    // Special cases to ensure any literal matches come first, no
	    // matter how unimportant they are. :)
	    if (a.nicelow == curr) return -1;
	    if (b.nicelow == curr) return 1;

	    // Otherwise, put them in importance order.
	    return a.uid - b.uid;
	};

	if (matches.length < 100) {
	    // We can just sort it and that'll be plenty fast.
	    return matches.sort(compare);
	}

	// Lots of elements -- do something fancier for more speed.  Since we
	// are only going to show 20 results, it is definitely safe to throw
	// away any entries whose UID is larger than some CUTOFF, as long as
	// CUTOFF is bigger than at least 20 UIDs.  So, gather a reasonable
	// subset of UIDs, sort them, and pick the 20th one.  Then throw away
	// everything past it in a linear sweep.
	var first_uids = [];
	for(var i = 0; i < 100; ++i) {
	    first_uids.push(matches[i].uid);
	}
	//console.log("Gathered up UIDs: ", first_uids);
	first_uids = first_uids.sort(function(a,b){ return a-b; });
	//console.log("Sorted UIDs:", first_uids);
	var cutoff = first_uids[19];

	var consider = [];
	for(var i = 0;i < matches.length; ++i) {
	    var entry = matches[i];
	    if (entry.nicelow == curr || entry.uid < cutoff) {
		consider.push(entry);
	    }
	}
	//console.log("Down to " + consider.length + " entries to consider:", consider);

	// Then we just sort whatever survived using our ordinary comparison
	// function, which now doesn't need to consider the vast majority of
	// the array.
	return consider.sort(compare);
    };

    engine1.initialize();

    $("#jump").typeahead({
			     highlight: true,
			     hint: true,
			     autoselect: true
			 },
			 {
			     name: "topics",
			     displayKey: 'nicename',
			     source: engine1.ttAdapter(),
			     templates:
			     {
				 suggestion: jumpRender
			     }
			 });

    $("#jump").bind('typeahead:selected', jumpGo);
    $("#jump").bind('typeahead:autocompleted', jumpGo);
    maybePowertip("#jumpmsg", {placement:'se'});
    $("#jump").attr("placeholder", "append");
    $("#jump").removeAttr("disabled");


    $("#jumpform").submit(function(event)
    {
	// Magic code that took me way too much hacking to get working.
	//console.log("In form submitter.");

	// Don't actually try to "submit" the form.
	event.preventDefault();

	// Act like the tab key was pressed, to trigger autocomplete.
	// In the case where the user hasn't entered the entire input,
	// this will trigger the jumpGo call all by itself.

	var e = jQuery.Event("keydown");
	e.keyCode = e.which = 9; // 9 == tab
	$("#jump").trigger(e);

	// We seem to never get here EXCEPT in the case where the user
	// has typed in the entire text for one of the entries.  In
	// that case, for whatever reason, the autocomplete feature
	// doesn't actually trigger the submit.  So, if we get here,
	// figure out what we're looking at and submit it manually.

	var value = $("#jump").typeahead('val');
	// console.log("After tab, value is " + value);
	jumpGo(null, {value:value});
    });
}

function jumpGo(obj,datum) {
    var key = datum["value"];
    if (topicExists(key)) {
        actionGoKey(key);
	$("#jump").typeahead('val', "");
	// $("#jump").typeahead('setQuery', '');
    }
    else {
        alert("Invalid key " + key);
    }
}

function searchInit() {
    $("#searchbox").attr("placeholder", "files");
    $("#searchbox").removeAttr("disabled");
}





function onIndexLoaded()
{
    xindexInit();

    if (XDATAGET == "") {
        // Load xdata.js after xindexInit() because that way we know the
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
        acc += "<a href=\"javascript:navFlatToChar('" + c + "')\">" + c + "</a>";
        if (c == "M")
            acc += "<br/>";
    }
    $("#letters").html(acc);

    var top_node = navMakeNode(TOP_KEY);
    $("#nav").html(top_node);
    navExpand(0);
    navActivateTooltip(0);

    jumpInit();
    searchInit();

    // Load katex after the other stuff is loaded.
    LazyLoad.js('lib/katex/katex.min.js', onKatexLoaded);
}

function onDataLoaded()
{
    xdata_loaded = true;
    var params = getPageParameters();

    // Make sure that BROKEN_KEY gets loaded early on, so we can always just
    // assume it is loaded.
    if (topicExists(BROKEN_KEY)) {
	xdataWhenReady([BROKEN_KEY], function() { return; });
    }

    if ("search" in params) {
	var str = params["search"];
	var str_url = encodeURIComponent(str);
	var str_html = htmlEncode(str);
	//console.log("onDataLoaded: search for " + str + " --> 0");
	window.history.replaceState({search:str,rtop:0},
				    str_html, "?search=" + str_url);
	searchGo(str);
    }

    else {
	var key = params["topic"] || TOP_KEY;
	if (!key.match(/^[A-Za-z0-9._\-]*$/)) {
	    $("#right").html("Illegal topic name, rejecting to prevent XSS attacks.");
	    return;
	}
	//console.log("onDataLoaded: key " + key + " --> 0");
	window.history.replaceState({key:key,rtop:0},
				    keyTitle(key), "?topic=" + key);
	datLoadKey(key, 0);
    }

    window.addEventListener('popstate',
                            function(event) {
				event.preventDefault();
                                actionGoBack(event.state);
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
    if (topicExists(key)) {
        rawname = topicRawname(key);
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
        "; manual.\n\n";

    window.open('data:application/x-acl2-xdoc-link;charset=utf-8,' +
    encodeURIComponent(srclink_header + rawname));
}

function actionGoKey(key) {

    // Warning: if you change this, check for all uses of replaceState,
    // pushState, and popState, and update them to match.

    if (!xdata_loaded) {
        pleaseWait();
        return;
    }

    // console.log("actionGoKey, going to new key " + key + " --> 0");
    historySavePlace();
    window.history.pushState({key:key,rtop:0}, keyTitle(key),
			     "?topic=" + key);
    datLoadKey(key, 0);

    // if we're in mobile mode, hide the navigation bar whenever the
    // user navigates to a new page.
    $("#left").removeClass("active");
    closeAllPowertips();
}

function historySavePlace() {
    var curr_state = history.state;
    var rtop = $("#right").scrollTop();
    if (curr_state) {
	// Safari doesn't seem to implement history.state
	//console.log("saving place: " + curr_state.key + " --> " + rtop);
	curr_state["rtop"] = rtop;
	window.history.replaceState(curr_state, "");
    }
}

function actionGoBack(data) {

    // Warning: if you change this, check for all uses of replaceState,
    // pushState, and popState, and update them to match.

    //console.log("Going back with data = " + data);

    if (!data) {
	// Browsers may do this when the page is initially loaded,
	// so ignore this event.
	// console.log("Empty data, so returning early.");
	return;
    }

    //console.log("actionGoBack data: search = " + data.search
    //            + ", key = " + data.key + ", rtop = " + data.rtop);

    // I want to do something like historySavePlace() here, so that
    // the forward button would also remember its place.  But that doesn't
    // worked.  All solutions to this problem look very complex, e.g.,
    // see http://stackoverflow.com/questions/14541398.  So, I give up,
    // no forward-button re-scrolling for you.

    if ("search" in data) {
	var str = data["search"];
	searchGo(str);
    }

    else if ("key" in data) {
	var key = data.key;
	var rtop = ("rtop" in data) ? data["rtop"] : 0;
	if (key) {
	    datLoadKey(key, rtop);
	}
    }
}



function printerFriendly()
{
    var w = window.open("", "Printer",
			"height=600,width=640,toolbar=1,location=0,resizable=1,scrollbars=1,status=0");

    var html = "<html>\n"
	+ "<head>\n"
	+ "<title>Printer Friendly</title>\n"
        + "<link rel=\"stylesheet\" type=\"text/css\" href=\"http://fonts.googleapis.com/css?family=Noto+Serif\">"
        + "<link rel=\"stylesheet\" type=\"text/css\" href=\"http://fonts.googleapis.com/css?family=Lato\">"
        + "<link rel=\"stylesheet\" type=\"text/css\" href=\"http://fonts.googleapis.com/css?family=Source+Code+Pro\">"
        + "<link rel=\"stylesheet\" type=\"text/css\" href=\"print.css\"/>"
        + "<link rel=\"shortcut icon\" href=\"favicon.png\"/>"
        + "</head><body>"
	+ $("#data").html()
	+ "</body></html>";

    w.document.write(html);

//    $(w.document.body).html(html);
}

function dolink(event, topic) {
    if (event.button == 1) {
	return true;
    }
    actionGoKey(topic);
    return false;
}
