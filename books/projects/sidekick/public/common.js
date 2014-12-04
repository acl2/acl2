/*

ACL2 Sidekick
Copyright (C) 2014 Kookamara LLC

Contact:

  Kookamara LLC
  11410 Windermere Meadows
  Austin, TX 78759, USA
  http://www.kookamara.com/

License: (An MIT/X11-style license)

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.

*/

function htmlEncode(value)
{
    // copied from stackoverflow:1219860
    return $('<div/>').text(value).html();
}

String.prototype.upcaseFirst = function () {
    var str = this;
    return str.charAt(0).toUpperCase() + str.slice(1);
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

function popup_disassemble(name) {
    var w = window.open("disassemble.html?name=" + name, "Disassembly_" + name,
	"height=600,width=640,toolbar=1,location=0,resizable=1,scrollbars=1,status=0");
}