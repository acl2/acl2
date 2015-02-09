// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

function log(msg) {
    "use strict";
    if (window.console && console.log) {
	console.log(msg);
    }
}

function assert(condition, message) {
    "use strict";
    // http://stackoverflow.com/questions/15313418/javascript-assert
    if (!condition) {
	message = message || "Assertion failed";
	if (typeof Error !== "undefined") { throw new Error(message); }
        throw message; // Fallback
    }
}

function htmlEncode(value) {
    "use strict";
    // http://stackoverflow.com/questions/1219860/html-encoding-in-javascript-jquery
    // http://jsperf.com/htmlencoderegex/17
    return document.createElement('a').appendChild(document.createTextNode(value)).parentNode.innerHTML;
}

function getParameterByName(name) {
    "use strict";
    name = name.replace(/[\[]/, "\\[").replace(/[\]]/, "\\]");
    var regex = new RegExp("[\\?&]" + name + "=([^&#]*)");
    var results = regex.exec(location.search);
    return results == null ? "" : decodeURIComponent(results[1].replace(/\+/g, " "));
}

var BASE  = getParameterByName("base");
var MODEL = getParameterByName("model");
assert(BASE,  "Expected base parameter");
assert(MODEL, "Expected model parameter");

function vlsGetJson(query) {
    "use strict";
    // Specialized wrapper for $.get() with tweaks for VLS commands.
    //   - Automatically fills in BASE and MODEL parameters
    //   - Assumes GET queries unless you specify:            type: "post"
    //   - Assumes the query is cacheable unless you specify: cache: false
    //
    // You can provide an optional ERROR callback with a single message
    // argument, but most commands can use the default handler (it just dies).
    //
    // We assumes VLS-FAIL/VLS-SUCCESS semantics.  That is, we expect the
    // resulting JSON object to have a ":ERROR" and ":VALUE" field.
    //  - If the ":ERROR" field is set, we invoke the error handler.
    //  - If the ":ERROR" field is NOT set, we invoke the success
    //    function on the ":VALUE".
    // The success callback therefore doesn't have to check for errors!
    log("vlsGetJson: Running query: "); log(query);

    assert(query,         "Null query?");
    assert(query.url,     "Query needs a URL.");
    assert(query.success, "Query has no success function?");

    var type  = "type"  in query ? query.type  : "get";
    var cache = "cache" in query ? query.cache : true;
    var data  = "data"  in query ? query.data  : {};
    assert(!("base" in data), "Query data shouldn't have its own 'base' parameter");
    assert(!("model" in data), "Query data shouldn't have its own 'model' parameter");
    data.base = BASE;
    data.model = MODEL;

    var userErrorCallback = "error" in query ? query.error : function(msg) {
	var body = "<pre>Error running query " + JSON.stringify(query) + "\n\n" + htmlEncode(msg) + "</pre>";
	$("body").html(body);
    }

    var ajaxQuery = { url: query.url,
		      cache: cache,
		      data: data,
		      type: type,
		      dataType: "json",
		      success: function(data, textStatus, jqXHR) {
			  assert(":ERROR" in data, "Query result has no :ERROR field");
			  if (data[":ERROR"]) {
			      userErrorCallback(data[":ERROR"]);
			      return;
			  }
			  assert(":VALUE" in data, "Query result has no :VALUE field");
			  query.success(data[":VALUE"]);
		      },
		      error: function(jqXHR, textStatus, errorThrown) {
			  userErrorCallback("Error running query: " + textStatus + "\n" + errorThrown);
		      }
		    };
    log("ajaxQuery: "); log(ajaxQuery);
    $.ajax(ajaxQuery);
}

function vlsGetHtml(query) {
    "use strict";
    // Similar to vlsGetJson but meant for HTML requests.
    assert(query,         "Null query?");
    assert(query.url,     "Query needs a URL.");
    assert(query.success, "Query has no success function?");

    var type  = "type"  in query ? query.type  : "get";
    var cache = "cache" in query ? query.cache : true;
    var data  = "data"  in query ? query.data  : [];
    assert(!("base" in data), "Query data shouldn't have its own 'base' parameter");
    assert(!("model" in data), "Query data shouldn't have its own 'model' parameter");
    data.base = BASE;
    data.model = MODEL;

    var userErrorCallback = "error" in query ? query.error : function(msg) {
	var body = "<pre>Error running query " + JSON.stringify(query) + "\n\n" + htmlEncode(msg) + "</pre>";
	$("body").html(body);
    }

    var ajaxQuery = { url: query.url,
		      cache: cache,
		      data: data,
		      type: type,
		      dataType: "html",
		      // Nothing fancy to do here with :ERROR and :VALUE, just
		      // use the user's success callback directly.
		      success: query.success,
		      error: function(jqXHR, textStatus, errorThrown) {
			  userErrorCallback("Error running query: " + textStatus + "\n" + errorThrown);
		      }
		    };
    $.ajax(ajaxQuery);
}



function alphanum(a, b) {
    "use strict";
    // Alphanumeric comparison (for nice sorting)
    // Credit: http://my.opera.com/GreyWyvern/blog/show.dml/1671288

    // Modification: make it case insensitive
    a = a.toLowerCase();
    b = b.toLowerCase();

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

function niceDescriptionType(type)
{
    "use strict";
    var niceType = (type == ":VL-MODULE") ? "module"
                 : (type == ":VL-PACKAGE") ? "package"
                 : (type == ":VL-INTERFACE") ? "interface"
                 : (type == ":VL-TYPEDEF") ? "typedef"
                 : (type == ":VL-PACKAGE") ? "package"
                 : (type == ":VL-FUNDECL") ? "function"
                 : (type == ":VL-PARAMDECL") ? "parameter"
                 : type;
    return niceType;
}

function jump_render(entry) {
    "use strict";
    var name = entry["value"];
    var type = entry["type"];
    var file = entry["file"];
    var line = entry["line"];
    var niceType = niceDescriptionType(type);

    return "<p><span class=\"sf\">" + name + "</span> &mdash; " + niceType + "<br/><small>" + file + ":" + line + "</small></p>";
}

var SUMMARY_DATA = false;
function withSummaryData(success, failure) {
    "use strict";
    if (SUMMARY_DATA) {
	success(SUMMARY_DATA);
    }
    else {
	$.ajax({
	    url: "/vls-get-summaries",
	    cache: true,
	    data: {"base":BASE, "model":MODEL},
	    dataType: "json",
	    type: "post",
	    success: function(data,textStatus,jqXHR) {
		var err = data[":ERROR"];
		if (err) {
		    failure(err);
		}
		else {
		    SUMMARY_DATA = data[":VALUE"];
		    success(SUMMARY_DATA);
		}
	    },
	    error: function()
	    {
		failure("Error invoking /vls-get-summaries");
	    }
	});
    }
}

function toolbarInitSuccess(summaries) {
    "use strict";
    log("toolbarInitSuccess");

    $(".toolbutton").powerTip({placement:'se',smartPlacement: true});
    $("#modelname").append("<p><b>" + MODEL + "</b><br/><small>" + BASE + "</small></p>");

    // Engine1 has only just the exact names
    var e1_data = [];
    for(var i = 0; i < SUMMARY_DATA.length; ++i) {
	var summary = summaries[i];
	summary["value"] = summary[":NAME"];
	var name = summary[":NAME"];
	var type = summary[":TYPE"];
	var file = summary[":FILE"];
	var line = summary[":LINE"];
	var entry = {"value":name, "type":type, "file":file, "line":line};
	e1_data.push(entry);
    }

    var engine1 = new Bloodhound({
	name: 'exact',
	local: e1_data,
	limit: 20,
	datumTokenizer: function (data) {
	    var name = data.value;
	    return [name];
	},
	queryTokenizer: Bloodhound.tokenizers.whitespace,
	sorter: function(a,b) { return alphanum(a.value,b.value); }
    });

    var e2_data = [];
    for(var i = 0;i < SUMMARY_DATA.length; ++i)
    {
	var summary = summaries[i];
	var name = summary[":NAME"];
	var type = summary[":TYPE"];
	var file = summary[":FILE"];
	var line = summary[":LINE"];
	var tokens1 = name.replace(/([a-z0-9])([A-Z])/g, '$1 $2').split(' '); // split up camelCaseNames
	var tokens2 = name.replace(/_/g, ' ').split(' ');                     // split up underscore_separated_names

	// merge all split up names, skipping name itself
	var tokens = [];
	var seen = [];
	seen[name] = 1;

	for(var j = 0; j < tokens1.length; ++j) {
	    var tok = tokens1[j];
	    if (tok && !seen[tok]) {
		tokens.push(tok);
		seen[tok] = 1;
	    }
	}

	for(var j = 0; j < tokens2.length; ++j) {
	    var tok = tokens2[j];
	    if (tok && !seen[tok]) {
		tokens.push(tok);
		seen[tok] = 1;
	    }
	}

	if (tokens.length != 0) {
	    var entry = {
		value: name,
		tokens: tokens,
		type: type,
		file: file,
		line: line
	    };
	    e2_data.push(entry);
	}
    }

    var engine2 = new Bloodhound({
	    name: 'fuzzy',
	    local: e2_data,
	    limit: 20,
	    datumTokenizer: function (data) {
		return data.tokens;
	    },
	    queryTokenizer: Bloodhound.tokenizers.whitespace,
	    sorter: function(a,b) { return alphanum(a.value,b.value); }
	});

    engine1.initialize();
    engine2.initialize();

    $("#jump").typeahead(
	{
	    highlight: true,
	    hint: true
	},
	{
	    name: 'exact',
	    displayKey: 'value',
	    source: engine1.ttAdapter(),
	    templates: { suggestion: jump_render }
	},
	{
	    name: 'fuzzy',
	    displayKey: 'value',
	    source: engine2.ttAdapter(),
	    templates: { suggestion: jump_render }
	}
    );

    $("#jump").bind('typeahead:selected', jump_go);
    $("#jump").bind('typeahead:autocompleted', jump_go);
    $("#jumpmsg").powerTip({placement:'se'});
    $("#jump").attr("placeholder", "fadd");
    $("#jump").removeAttr("disabled");

    $("#jumpform").submit(
	function(event)
	{
	    // Magic code that took me way too much hacking to get working.
	    // log("In form submitter.");

	    // Don't actually try to "submit" the form.
	    event.preventDefault();

	    // Act like the tab key was pressed, to trigger autocomplete.
	    // In the case where the user hasn't entered the entire input,
	    // this will trigger the jump_go call all by itself.

	    var e = jQuery.Event("keydown");
	    e.keyCode = e.which = 9; // 9 == tab
	    $("#jump").trigger(e);

	    // We seem to never get here EXCEPT in the case where the user
	    // has typed in the entire text for one of the entries.  In
	    // that case, for whatever reason, the autocomplete feature
	    // doesn't actually trigger the submit.  So, if we get here,
	    // figure out what we're looking at and submit it manually.

	    var value = $("#jump").typeahead('val');
	    // log("After tab, value is " + value);
	    jump_go(null, {value:value});
	}
    );
}

function toolbarInitFail(msg) {
    "use strict";
    $("#jump").attr("placeholder", msg);
}


function toolbar_init() {
    "use strict";
    create_toolbar();
    withSummaryData(toolbarInitSuccess, toolbarInitFail);
}

function jump_go(obj,datum) {
    "use strict";
    var key = datum["value"];
    log("jump_go(" + key + ")");
    window.location = "/display.html?base=" + BASE + "&model=" + MODEL + "&origname=" + key;
}


function connect(onReady) {
    "use strict";
    log("Connecting to base " + BASE + ", model " + MODEL);
    // Sanity check to make sure that the model is loaded.
    vlsGetJson({ url: "/load-model",
		 type: "post",
		 cache: false,
		 success: function(value) {
		     assert(":STATUS" in value);
		     var status = value[":STATUS"];
		     log("Model status: " + status);
		     if (status == ":LOADED") {
			 onReady();
		     }
		     else if (status == ":STARTED") {
			 var msg = "<h1>Model not loaded</h1>";
			 msg += "<h3>Base " + htmlEncode(BASE) + ", Model " + htmlEncode(MODEL) + "</h3>";
			 msg += "<p>This model is either invalid or not yet loaded.</p>";
			 msg += "<p>Maybe that idiot Jared restarted the VL server on you?</p>";
			 msg += "<p>You probably want to <a href='index.html'>go to model chooser</a></p>";
			 $("head").append("<link rel='stylesheet' href='style.css'/>");
			 $("body").html(msg);
		     }
		     else {
			 assert(false, "Unrecognized status " + status);
		     }
		 }});
}


function create_toolbar () {
    "use strict";
    var tb = "";
    tb += "<form id='jumpform'>";
    tb += "  <div id='icons'>";
    tb += "	<table width='100%'>";
    tb += "	<tr>";
    tb += "	  <td id='modelname' width=\"20%\">";
    tb += "	    <a href='index.html'>";
    tb += "	      <img src='images/choosemodel.png' class='toolbutton' align='left' data-powertip='<p>Switch to a different model.</p>'>";
    tb += "	    </a>";
    tb += "	  </td>";
    tb += "	  <td id='statuslink'>";
    tb += "	    <a href='status.html?base=" + BASE + "&model=" + MODEL + "'>";
    tb += "	      <img src='images/status.png' class='toolbutton' align='left' data-powertip='<p>Translation overview.</p>'>";
    tb += "	    </a>";
    tb += "	  </td>";

    tb += "	<td width=\"20%\">&nbsp;</td>";

    tb += "	  <td align='right'>";
    tb += "	    <nobr><label id='jumpmsg'> Jump to </label></nobr>";
    tb += "	  </td>";

    tb += "	  <td>";
    tb += "	    <input id='jump' class='typeahead' dtype='text' placeholder='loading...' disabled='disabled'/>";
    tb += "	    <input type='submit' style='visibility: hidden; position: fixed'/>";
    tb += "	  </td>";


    tb += "	<td width=\"10%\">&nbsp;</td>";

    tb += "	</tr>";
    tb += "      </table>";
    tb += "  </div>";
    tb += "</form>";
    $("#toolbar").html(tb);
}


function showLoc(file,line,col) {
    "use strict";
    var url = "loc.html?"
                  + "&base=" + BASE
                  + "&model=" + MODEL
                  + "&file=" + file
     	          + "&line=" + line
	          + "&col=" + col;
    var opts = "status=0,toolbar=1,height=500,width=780,resizable=1,scrollbars=1,location=1";
    var win = window.open(url, "locWindow", opts);
    win.focus();
    return false;
}




