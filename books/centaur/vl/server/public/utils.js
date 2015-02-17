// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
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

function vlsGetJson(query) {
    "use strict";
    // Specialized wrapper for $.get() with tweaks for VLS commands.
    //   - Automatically fills in MODEL parameter
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
    assert(!("model" in data), "Query data shouldn't have its own 'model' parameter");
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
    assert(!("model" in data), "Query data shouldn't have its own 'model' parameter");
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
