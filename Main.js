"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return _3;},_5=function(_6,_7,_){var _8=B(A1(_6,_)),_9=B(A1(_7,_));return new T(function(){return B(A1(_8,_9));});},_a=function(_b,_c,_){var _d=B(A1(_c,_));return _b;},_e=function(_f,_g,_){var _h=B(A1(_g,_));return new T(function(){return B(A1(_f,_h));});},_i=new T2(0,_e,_a),_j=function(_k,_){return _k;},_l=function(_m,_n,_){var _o=B(A1(_m,_));return new F(function(){return A1(_n,_);});},_p=new T5(0,_i,_j,_5,_l,_0),_q=new T(function(){return B(unCStr("base"));}),_r=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_s=new T(function(){return B(unCStr("IOException"));}),_t=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_q,_r,_s),_u=__Z,_v=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_t,_u,_u),_w=function(_x){return E(_v);},_y=function(_z){return E(E(_z).a);},_A=function(_B,_C,_D){var _E=B(A1(_B,_)),_F=B(A1(_C,_)),_G=hs_eqWord64(_E.a,_F.a);if(!_G){return __Z;}else{var _H=hs_eqWord64(_E.b,_F.b);return (!_H)?__Z:new T1(1,_D);}},_I=function(_J){var _K=E(_J);return new F(function(){return _A(B(_y(_K.a)),_w,_K.b);});},_L=new T(function(){return B(unCStr(": "));}),_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(unCStr(" ("));}),_O=function(_P,_Q){var _R=E(_P);return (_R._==0)?E(_Q):new T2(1,_R.a,new T(function(){return B(_O(_R.b,_Q));}));},_S=new T(function(){return B(unCStr("interrupted"));}),_T=new T(function(){return B(unCStr("system error"));}),_U=new T(function(){return B(unCStr("unsatisified constraints"));}),_V=new T(function(){return B(unCStr("user error"));}),_W=new T(function(){return B(unCStr("permission denied"));}),_X=new T(function(){return B(unCStr("illegal operation"));}),_Y=new T(function(){return B(unCStr("end of file"));}),_Z=new T(function(){return B(unCStr("resource exhausted"));}),_10=new T(function(){return B(unCStr("resource busy"));}),_11=new T(function(){return B(unCStr("does not exist"));}),_12=new T(function(){return B(unCStr("already exists"));}),_13=new T(function(){return B(unCStr("resource vanished"));}),_14=new T(function(){return B(unCStr("timeout"));}),_15=new T(function(){return B(unCStr("unsupported operation"));}),_16=new T(function(){return B(unCStr("hardware fault"));}),_17=new T(function(){return B(unCStr("inappropriate type"));}),_18=new T(function(){return B(unCStr("invalid argument"));}),_19=new T(function(){return B(unCStr("failed"));}),_1a=new T(function(){return B(unCStr("protocol error"));}),_1b=function(_1c,_1d){switch(E(_1c)){case 0:return new F(function(){return _O(_12,_1d);});break;case 1:return new F(function(){return _O(_11,_1d);});break;case 2:return new F(function(){return _O(_10,_1d);});break;case 3:return new F(function(){return _O(_Z,_1d);});break;case 4:return new F(function(){return _O(_Y,_1d);});break;case 5:return new F(function(){return _O(_X,_1d);});break;case 6:return new F(function(){return _O(_W,_1d);});break;case 7:return new F(function(){return _O(_V,_1d);});break;case 8:return new F(function(){return _O(_U,_1d);});break;case 9:return new F(function(){return _O(_T,_1d);});break;case 10:return new F(function(){return _O(_1a,_1d);});break;case 11:return new F(function(){return _O(_19,_1d);});break;case 12:return new F(function(){return _O(_18,_1d);});break;case 13:return new F(function(){return _O(_17,_1d);});break;case 14:return new F(function(){return _O(_16,_1d);});break;case 15:return new F(function(){return _O(_15,_1d);});break;case 16:return new F(function(){return _O(_14,_1d);});break;case 17:return new F(function(){return _O(_13,_1d);});break;default:return new F(function(){return _O(_S,_1d);});}},_1e=new T(function(){return B(unCStr("}"));}),_1f=new T(function(){return B(unCStr("{handle: "));}),_1g=function(_1h,_1i,_1j,_1k,_1l,_1m){var _1n=new T(function(){var _1o=new T(function(){var _1p=new T(function(){var _1q=E(_1k);if(!_1q._){return E(_1m);}else{var _1r=new T(function(){return B(_O(_1q,new T(function(){return B(_O(_M,_1m));},1)));},1);return B(_O(_N,_1r));}},1);return B(_1b(_1i,_1p));}),_1s=E(_1j);if(!_1s._){return E(_1o);}else{return B(_O(_1s,new T(function(){return B(_O(_L,_1o));},1)));}}),_1t=E(_1l);if(!_1t._){var _1u=E(_1h);if(!_1u._){return E(_1n);}else{var _1v=E(_1u.a);if(!_1v._){var _1w=new T(function(){var _1x=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1x));},1);return new F(function(){return _O(_1f,_1w);});}else{var _1y=new T(function(){var _1z=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1z));},1);return new F(function(){return _O(_1f,_1y);});}}}else{return new F(function(){return _O(_1t.a,new T(function(){return B(_O(_L,_1n));},1));});}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1g(_1C.a,_1C.b,_1C.c,_1C.d,_1C.f,_u);});},_1D=function(_1E){return new T2(0,_1F,_1E);},_1G=function(_1H,_1I,_1J){var _1K=E(_1I);return new F(function(){return _1g(_1K.a,_1K.b,_1K.c,_1K.d,_1K.f,_1J);});},_1L=function(_1M,_1N){var _1O=E(_1M);return new F(function(){return _1g(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_1N);});},_1P=44,_1Q=93,_1R=91,_1S=function(_1T,_1U,_1V){var _1W=E(_1U);if(!_1W._){return new F(function(){return unAppCStr("[]",_1V);});}else{var _1X=new T(function(){var _1Y=new T(function(){var _1Z=function(_20){var _21=E(_20);if(!_21._){return E(new T2(1,_1Q,_1V));}else{var _22=new T(function(){return B(A2(_1T,_21.a,new T(function(){return B(_1Z(_21.b));})));});return new T2(1,_1P,_22);}};return B(_1Z(_1W.b));});return B(A2(_1T,_1W.a,_1Y));});return new T2(1,_1R,_1X);}},_23=function(_24,_25){return new F(function(){return _1S(_1L,_24,_25);});},_26=new T3(0,_1G,_1A,_23),_1F=new T(function(){return new T5(0,_w,_26,_1D,_I,_1A);}),_27=new T(function(){return E(_1F);}),_28=function(_29){return E(E(_29).c);},_2a=__Z,_2b=7,_2c=function(_2d){return new T6(0,_2a,_2b,_u,_2d,_2a,_2a);},_2e=function(_2f,_){var _2g=new T(function(){return B(A2(_28,_27,new T(function(){return B(A1(_2c,_2f));})));});return new F(function(){return die(_2g);});},_2h=function(_2i,_){return new F(function(){return _2e(_2i,_);});},_2j=function(_2k){return new F(function(){return A1(_2h,_2k);});},_2l=function(_2m,_2n,_){var _2o=B(A1(_2m,_));return new F(function(){return A2(_2n,_2o,_);});},_2p=new T5(0,_p,_2l,_l,_j,_2j),_2q=function(_2r){return E(_2r);},_2s=new T2(0,_2p,_2q),_2t=0,_2u=new T(function(){return B(unCStr("Months"));}),_2v=new T(function(){return B(unCStr("Day"));}),_2w=new T(function(){return B(unCStr("Hour"));}),_2x=new T(function(){return B(unCStr("Starting"));}),_2y=function(_2z){return new F(function(){return err(B(unAppCStr("Haste.JSON.!: unable to look up key ",new T(function(){return fromJSStr(E(_2z));}))));});},_2A=function(_2B){return E(E(_2B).a);},_2C=function(_2D,_2E){return (!B(A3(_2A,_2F,_2D,_2E)))?true:false;},_2G=function(_2H,_2I){var _2J=strEq(E(_2H),E(_2I));return (E(_2J)==0)?false:true;},_2K=function(_2L,_2M){return new F(function(){return _2G(_2L,_2M);});},_2F=new T(function(){return new T2(0,_2K,_2C);}),_2N=function(_2O,_2P,_2Q){while(1){var _2R=E(_2Q);if(!_2R._){return __Z;}else{var _2S=E(_2R.a);if(!B(A3(_2A,_2O,_2P,_2S.a))){_2Q=_2R.b;continue;}else{return new T1(1,_2S.b);}}}},_2T=function(_2U,_2V){var _2W=E(_2U);if(_2W._==4){var _2X=B(_2N(_2F,_2V,_2W.a));if(!_2X._){return new F(function(){return _2y(_2V);});}else{return E(_2X.a);}}else{return new F(function(){return _2y(_2V);});}},_2Y=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_2Z=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_30=new T1(1,_2t),_31="()",_32=function(_33){var _34=strEq(_33,E(_31));return (E(_34)==0)?__Z:E(_30);},_35=function(_36){return new F(function(){return _32(E(_36));});},_37=function(_38){return E(_31);},_39=new T2(0,_37,_35),_3a=function(_3b){return new F(function(){return jsParseJSON(E(_3b));});},_3c="]",_3d="}",_3e=":",_3f=",",_3g=new T(function(){return eval("JSON.stringify");}),_3h="false",_3i="null",_3j="[",_3k="{",_3l="\"",_3m="true",_3n=function(_3o,_3p){var _3q=E(_3p);switch(_3q._){case 0:return new T2(0,new T(function(){return jsShow(_3q.a);}),_3o);case 1:return new T2(0,new T(function(){var _3r=__app1(E(_3g),_3q.a);return String(_3r);}),_3o);case 2:return (!E(_3q.a))?new T2(0,_3h,_3o):new T2(0,_3m,_3o);case 3:var _3s=E(_3q.a);if(!_3s._){return new T2(0,_3j,new T2(1,_3c,_3o));}else{var _3t=new T(function(){var _3u=new T(function(){var _3v=function(_3w){var _3x=E(_3w);if(!_3x._){return E(new T2(1,_3c,_3o));}else{var _3y=new T(function(){var _3z=B(_3n(new T(function(){return B(_3v(_3x.b));}),_3x.a));return new T2(1,_3z.a,_3z.b);});return new T2(1,_3f,_3y);}};return B(_3v(_3s.b));}),_3A=B(_3n(_3u,_3s.a));return new T2(1,_3A.a,_3A.b);});return new T2(0,_3j,_3t);}break;case 4:var _3B=E(_3q.a);if(!_3B._){return new T2(0,_3k,new T2(1,_3d,_3o));}else{var _3C=E(_3B.a),_3D=new T(function(){var _3E=new T(function(){var _3F=function(_3G){var _3H=E(_3G);if(!_3H._){return E(new T2(1,_3d,_3o));}else{var _3I=E(_3H.a),_3J=new T(function(){var _3K=B(_3n(new T(function(){return B(_3F(_3H.b));}),_3I.b));return new T2(1,_3K.a,_3K.b);});return new T2(1,_3f,new T2(1,_3l,new T2(1,_3I.a,new T2(1,_3l,new T2(1,_3e,_3J)))));}};return B(_3F(_3B.b));}),_3L=B(_3n(_3E,_3C.b));return new T2(1,_3L.a,_3L.b);});return new T2(0,_3k,new T2(1,new T(function(){var _3M=__app1(E(_3g),E(_3C.a));return String(_3M);}),new T2(1,_3e,_3D)));}break;default:return new T2(0,_3i,_3o);}},_3N=new T(function(){return toJSStr(_u);}),_3O=function(_3P){var _3Q=B(_3n(_u,_3P)),_3R=jsCat(new T2(1,_3Q.a,_3Q.b),E(_3N));return E(_3R);},_3S=function(_3T){return new F(function(){return _3O(_3T);});},_3U=new T2(0,_3S,_3a),_3V=function(_){return _2t;},_3W=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_3X=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_3Y=function(_3Z,_40,_){var _41=__app1(E(_3W),_40),_42=B(A2(_3Z,_40,_)),_43=__app1(E(_3X),_40);return new F(function(){return _3V(_);});},_44=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_45=function(_46,_47,_){var _48=__app1(E(_3W),_47),_49=B(A2(_46,_47,_)),_4a=__app1(E(_44),_47);return new F(function(){return _3V(_);});},_4b=function(_4c,_4d){while(1){var _4e=E(_4c);if(!_4e._){return E(_4d);}else{var _4f=_4d+1|0;_4c=_4e.b;_4d=_4f;continue;}}},_4g=function(_4h,_4i){var _4j=E(_4i);if(!_4j._){return __Z;}else{var _4k=_4j.a,_4l=E(_4h);return (_4l==1)?new T2(1,_4k,_u):new T2(1,_4k,new T(function(){return B(_4g(_4l-1|0,_4j.b));}));}},_4m=function(_4n,_4o){while(1){var _4p=E(_4n);if(!_4p._){return E(_4o);}else{var _4q=new T2(1,_4p.a,_4o);_4n=_4p.b;_4o=_4q;continue;}}},_4r=new T(function(){return B(_4m(_u,_u));}),_4s=function(_4t,_4u){if(0>=_4t){return E(_4r);}else{return new F(function(){return _4m(B(_4g(_4t,B(_4m(_4u,_u)))),_u);});}},_4v=0,_4w=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_4x=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_4y=function(_4z,_4A,_){var _4B=E(_4z);if(!_4B._){return _2t;}else{var _4C=E(_4B.a),_4D=E(_4A),_4E=__app3(E(_4w),_4D,E(_4C.a),E(_4C.b)),_4F=E(_4B.b);if(!_4F._){return _2t;}else{var _4G=E(_4F.a),_4H=E(_4x),_4I=__app3(_4H,_4D,E(_4G.a),E(_4G.b)),_4J=function(_4K,_){while(1){var _4L=E(_4K);if(!_4L._){return _2t;}else{var _4M=E(_4L.a),_4N=__app3(_4H,_4D,E(_4M.a),E(_4M.b));_4K=_4L.b;continue;}}};return new F(function(){return _4J(_4F.b,_);});}}},_4O=800,_4P=50,_4Q=new T2(0,_4O,_4P),_4R=new T2(1,_4Q,_u),_4S=0,_4T=new T2(0,_4S,_4P),_4U=new T2(1,_4T,_4R),_4V=100,_4W=new T2(0,_4O,_4V),_4X=new T2(1,_4W,_u),_4Y=new T2(0,_4S,_4V),_4Z=new T2(1,_4Y,_4X),_50=150,_51=new T2(0,_4O,_50),_52=new T2(1,_51,_u),_53=new T2(0,_4S,_50),_54=new T2(1,_53,_52),_55=200,_56=new T2(0,_4O,_55),_57=new T2(1,_56,_u),_58=new T2(0,_4S,_55),_59=new T2(1,_58,_57),_5a=250,_5b=new T2(0,_4O,_5a),_5c=new T2(1,_5b,_u),_5d=new T2(0,_4S,_5a),_5e=new T2(1,_5d,_5c),_5f=function(_5g,_){var _5h=B(_4y(_5e,_5g,_)),_5i=B(_4y(_59,_5g,_)),_5j=B(_4y(_54,_5g,_)),_5k=B(_4y(_4Z,_5g,_));return new F(function(){return _4y(_4U,_5g,_);});},_5l="POST",_5m="GET",_5n="=",_5o="&",_5p=function(_5q,_5r){var _5s=E(_5r);return (_5s._==0)?__Z:new T2(1,new T(function(){return B(A1(_5q,_5s.a));}),new T(function(){return B(_5p(_5q,_5s.b));}));},_5t=function(_5u){return E(E(_5u).a);},_5v=function(_5w,_5x,_5y){var _5z=function(_5A){var _5B=E(_5A);return new F(function(){return jsCat(new T2(1,new T(function(){return B(A2(_5t,_5w,_5B.a));}),new T2(1,new T(function(){return B(A2(_5t,_5x,_5B.b));}),_u)),E(_5n));});},_5C=jsCat(B(_5p(_5z,_5y)),E(_5o));return E(_5C);},_5D=new T(function(){return eval("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");}),_5E=function(_5F){return E(E(_5F).b);},_5G=function(_){return new F(function(){return __jsNull();});},_5H=function(_5I){var _5J=B(A1(_5I,_));return E(_5J);},_5K=new T(function(){return B(_5H(_5G));}),_5L=new T(function(){return E(_5K);}),_5M=function(_5N){return E(E(_5N).b);},_5O=new T(function(){return toJSStr(_u);}),_5P="?",_5Q=function(_5R){return new F(function(){return toJSStr(E(_5R));});},_5S=function(_5T,_5U,_5V,_5W,_5X,_5Y,_5Z,_60){var _61=new T(function(){return B(_5v(_5U,_5V,_5Z));}),_62=new T(function(){return B(_5Q(_5Y));}),_63=function(_){var _64=function(_65){var _66=function(_67){var _68=function(_69){var _6a=new T(function(){return B(_5E(_5W));}),_6b=function(_6c,_){var _6d=new T(function(){var _6e=E(_6c),_6f=__eq(_6e,E(_5L));if(!E(_6f)){return B(A1(_6a,new T(function(){return String(_6e);})));}else{return __Z;}}),_6g=B(A2(_60,_6d,_));return _5L;},_6h=__createJSFunc(2,E(_6b)),_6i=__app5(E(_5D),_65,_67,true,_69,_6h);return _2t;};if(!E(_5X)){return new F(function(){return _68(E(_5O));});}else{var _6j=E(_5Z);if(!_6j._){return new F(function(){return _68(E(_5O));});}else{return new F(function(){return _68(B(_5v(_5U,_5V,_6j)));});}}};if(!E(_5X)){if(!E(_5Z)._){return new F(function(){return _66(toJSStr(E(_5Y)));});}else{var _6k=jsCat(new T2(1,_62,new T2(1,_61,_u)),E(_5P));return new F(function(){return _66(_6k);});}}else{return new F(function(){return _66(toJSStr(E(_5Y)));});}};if(!E(_5X)){return new F(function(){return _64(E(_5m));});}else{return new F(function(){return _64(E(_5l));});}};return new F(function(){return A2(_5M,_5T,_63);});},_6l=new T(function(){return B(unCStr(": empty list"));}),_6m=new T(function(){return B(unCStr("Prelude."));}),_6n=function(_6o){return new F(function(){return err(B(_O(_6m,new T(function(){return B(_O(_6o,_6l));},1))));});},_6p=new T(function(){return B(unCStr("head"));}),_6q=new T(function(){return B(_6n(_6p));}),_6r=new T(function(){return eval("(function(e){e.width = e.width;})");}),_6s=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_6t=new T(function(){return B(err(_6s));}),_6u=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_6v=new T(function(){return B(err(_6u));}),_6w=new T(function(){return B(unCStr("base"));}),_6x=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6y=new T(function(){return B(unCStr("PatternMatchFail"));}),_6z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6w,_6x,_6y),_6A=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6z,_u,_u),_6B=function(_6C){return E(_6A);},_6D=function(_6E){var _6F=E(_6E);return new F(function(){return _A(B(_y(_6F.a)),_6B,_6F.b);});},_6G=function(_6H){return E(E(_6H).a);},_6I=function(_6J){return new T2(0,_6K,_6J);},_6L=function(_6M,_6N){return new F(function(){return _O(E(_6M).a,_6N);});},_6O=function(_6P,_6Q){return new F(function(){return _1S(_6L,_6P,_6Q);});},_6R=function(_6S,_6T,_6U){return new F(function(){return _O(E(_6T).a,_6U);});},_6V=new T3(0,_6R,_6G,_6O),_6K=new T(function(){return new T5(0,_6B,_6V,_6I,_6D,_6G);}),_6W=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6X=function(_6Y,_6Z){return new F(function(){return die(new T(function(){return B(A2(_28,_6Z,_6Y));}));});},_70=function(_71,_72){return new F(function(){return _6X(_71,_72);});},_73=function(_74,_75){var _76=E(_75);if(!_76._){return new T2(0,_u,_u);}else{var _77=_76.a;if(!B(A1(_74,_77))){return new T2(0,_u,_76);}else{var _78=new T(function(){var _79=B(_73(_74,_76.b));return new T2(0,_79.a,_79.b);});return new T2(0,new T2(1,_77,new T(function(){return E(E(_78).a);})),new T(function(){return E(E(_78).b);}));}}},_7a=32,_7b=new T(function(){return B(unCStr("\n"));}),_7c=function(_7d){return (E(_7d)==124)?false:true;},_7e=function(_7f,_7g){var _7h=B(_73(_7c,B(unCStr(_7f)))),_7i=_7h.a,_7j=function(_7k,_7l){var _7m=new T(function(){var _7n=new T(function(){return B(_O(_7g,new T(function(){return B(_O(_7l,_7b));},1)));});return B(unAppCStr(": ",_7n));},1);return new F(function(){return _O(_7k,_7m);});},_7o=E(_7h.b);if(!_7o._){return new F(function(){return _7j(_7i,_u);});}else{if(E(_7o.a)==124){return new F(function(){return _7j(_7i,new T2(1,_7a,_7o.b));});}else{return new F(function(){return _7j(_7i,_u);});}}},_7p=function(_7q){return new F(function(){return _70(new T1(0,new T(function(){return B(_7e(_7q,_6W));})),_6K);});},_7r=new T(function(){return B(_7p("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7s=function(_7t,_7u){while(1){var _7v=B((function(_7w,_7x){var _7y=E(_7w);switch(_7y._){case 0:var _7z=E(_7x);if(!_7z._){return __Z;}else{_7t=B(A1(_7y.a,_7z.a));_7u=_7z.b;return __continue;}break;case 1:var _7A=B(A1(_7y.a,_7x)),_7B=_7x;_7t=_7A;_7u=_7B;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_7y.a,_7x),new T(function(){return B(_7s(_7y.b,_7x));}));default:return E(_7y.a);}})(_7t,_7u));if(_7v!=__continue){return _7v;}}},_7C=function(_7D,_7E){var _7F=function(_7G){var _7H=E(_7E);if(_7H._==3){return new T2(3,_7H.a,new T(function(){return B(_7C(_7D,_7H.b));}));}else{var _7I=E(_7D);if(_7I._==2){return E(_7H);}else{var _7J=E(_7H);if(_7J._==2){return E(_7I);}else{var _7K=function(_7L){var _7M=E(_7J);if(_7M._==4){var _7N=function(_7O){return new T1(4,new T(function(){return B(_O(B(_7s(_7I,_7O)),_7M.a));}));};return new T1(1,_7N);}else{var _7P=E(_7I);if(_7P._==1){var _7Q=_7P.a,_7R=E(_7M);if(!_7R._){return new T1(1,function(_7S){return new F(function(){return _7C(B(A1(_7Q,_7S)),_7R);});});}else{var _7T=function(_7U){return new F(function(){return _7C(B(A1(_7Q,_7U)),new T(function(){return B(A1(_7R.a,_7U));}));});};return new T1(1,_7T);}}else{var _7V=E(_7M);if(!_7V._){return E(_7r);}else{var _7W=function(_7X){return new F(function(){return _7C(_7P,new T(function(){return B(A1(_7V.a,_7X));}));});};return new T1(1,_7W);}}}},_7Y=E(_7I);switch(_7Y._){case 1:var _7Z=E(_7J);if(_7Z._==4){var _80=function(_81){return new T1(4,new T(function(){return B(_O(B(_7s(B(A1(_7Y.a,_81)),_81)),_7Z.a));}));};return new T1(1,_80);}else{return new F(function(){return _7K(_);});}break;case 4:var _82=_7Y.a,_83=E(_7J);switch(_83._){case 0:var _84=function(_85){var _86=new T(function(){return B(_O(_82,new T(function(){return B(_7s(_83,_85));},1)));});return new T1(4,_86);};return new T1(1,_84);case 1:var _87=function(_88){var _89=new T(function(){return B(_O(_82,new T(function(){return B(_7s(B(A1(_83.a,_88)),_88));},1)));});return new T1(4,_89);};return new T1(1,_87);default:return new T1(4,new T(function(){return B(_O(_82,_83.a));}));}break;default:return new F(function(){return _7K(_);});}}}}},_8a=E(_7D);switch(_8a._){case 0:var _8b=E(_7E);if(!_8b._){var _8c=function(_8d){return new F(function(){return _7C(B(A1(_8a.a,_8d)),new T(function(){return B(A1(_8b.a,_8d));}));});};return new T1(0,_8c);}else{return new F(function(){return _7F(_);});}break;case 3:return new T2(3,_8a.a,new T(function(){return B(_7C(_8a.b,_7E));}));default:return new F(function(){return _7F(_);});}},_8e=new T(function(){return B(unCStr("("));}),_8f=new T(function(){return B(unCStr(")"));}),_8g=function(_8h,_8i){while(1){var _8j=E(_8h);if(!_8j._){return (E(_8i)._==0)?true:false;}else{var _8k=E(_8i);if(!_8k._){return false;}else{if(E(_8j.a)!=E(_8k.a)){return false;}else{_8h=_8j.b;_8i=_8k.b;continue;}}}}},_8l=function(_8m,_8n){return E(_8m)!=E(_8n);},_8o=function(_8p,_8q){return E(_8p)==E(_8q);},_8r=new T2(0,_8o,_8l),_8s=function(_8t,_8u){while(1){var _8v=E(_8t);if(!_8v._){return (E(_8u)._==0)?true:false;}else{var _8w=E(_8u);if(!_8w._){return false;}else{if(E(_8v.a)!=E(_8w.a)){return false;}else{_8t=_8v.b;_8u=_8w.b;continue;}}}}},_8x=function(_8y,_8z){return (!B(_8s(_8y,_8z)))?true:false;},_8A=new T2(0,_8s,_8x),_8B=function(_8C,_8D){var _8E=E(_8C);switch(_8E._){case 0:return new T1(0,function(_8F){return new F(function(){return _8B(B(A1(_8E.a,_8F)),_8D);});});case 1:return new T1(1,function(_8G){return new F(function(){return _8B(B(A1(_8E.a,_8G)),_8D);});});case 2:return new T0(2);case 3:return new F(function(){return _7C(B(A1(_8D,_8E.a)),new T(function(){return B(_8B(_8E.b,_8D));}));});break;default:var _8H=function(_8I){var _8J=E(_8I);if(!_8J._){return __Z;}else{var _8K=E(_8J.a);return new F(function(){return _O(B(_7s(B(A1(_8D,_8K.a)),_8K.b)),new T(function(){return B(_8H(_8J.b));},1));});}},_8L=B(_8H(_8E.a));return (_8L._==0)?new T0(2):new T1(4,_8L);}},_8M=new T0(2),_8N=function(_8O){return new T2(3,_8O,_8M);},_8P=function(_8Q,_8R){var _8S=E(_8Q);if(!_8S){return new F(function(){return A1(_8R,_2t);});}else{var _8T=new T(function(){return B(_8P(_8S-1|0,_8R));});return new T1(0,function(_8U){return E(_8T);});}},_8V=function(_8W,_8X,_8Y){var _8Z=new T(function(){return B(A1(_8W,_8N));}),_90=function(_91,_92,_93,_94){while(1){var _95=B((function(_96,_97,_98,_99){var _9a=E(_96);switch(_9a._){case 0:var _9b=E(_97);if(!_9b._){return new F(function(){return A1(_8X,_99);});}else{var _9c=_98+1|0,_9d=_99;_91=B(A1(_9a.a,_9b.a));_92=_9b.b;_93=_9c;_94=_9d;return __continue;}break;case 1:var _9e=B(A1(_9a.a,_97)),_9f=_97,_9c=_98,_9d=_99;_91=_9e;_92=_9f;_93=_9c;_94=_9d;return __continue;case 2:return new F(function(){return A1(_8X,_99);});break;case 3:var _9g=new T(function(){return B(_8B(_9a,_99));});return new F(function(){return _8P(_98,function(_9h){return E(_9g);});});break;default:return new F(function(){return _8B(_9a,_99);});}})(_91,_92,_93,_94));if(_95!=__continue){return _95;}}};return function(_9i){return new F(function(){return _90(_8Z,_9i,0,_8Y);});};},_9j=function(_9k){return new F(function(){return A1(_9k,_u);});},_9l=function(_9m,_9n){var _9o=function(_9p){var _9q=E(_9p);if(!_9q._){return E(_9j);}else{var _9r=_9q.a;if(!B(A1(_9m,_9r))){return E(_9j);}else{var _9s=new T(function(){return B(_9o(_9q.b));}),_9t=function(_9u){var _9v=new T(function(){return B(A1(_9s,function(_9w){return new F(function(){return A1(_9u,new T2(1,_9r,_9w));});}));});return new T1(0,function(_9x){return E(_9v);});};return E(_9t);}}};return function(_9y){return new F(function(){return A2(_9o,_9y,_9n);});};},_9z=new T0(6),_9A=new T(function(){return B(unCStr("valDig: Bad base"));}),_9B=new T(function(){return B(err(_9A));}),_9C=function(_9D,_9E){var _9F=function(_9G,_9H){var _9I=E(_9G);if(!_9I._){var _9J=new T(function(){return B(A1(_9H,_u));});return function(_9K){return new F(function(){return A1(_9K,_9J);});};}else{var _9L=E(_9I.a),_9M=function(_9N){var _9O=new T(function(){return B(_9F(_9I.b,function(_9P){return new F(function(){return A1(_9H,new T2(1,_9N,_9P));});}));}),_9Q=function(_9R){var _9S=new T(function(){return B(A1(_9O,_9R));});return new T1(0,function(_9T){return E(_9S);});};return E(_9Q);};switch(E(_9D)){case 8:if(48>_9L){var _9U=new T(function(){return B(A1(_9H,_u));});return function(_9V){return new F(function(){return A1(_9V,_9U);});};}else{if(_9L>55){var _9W=new T(function(){return B(A1(_9H,_u));});return function(_9X){return new F(function(){return A1(_9X,_9W);});};}else{return new F(function(){return _9M(_9L-48|0);});}}break;case 10:if(48>_9L){var _9Y=new T(function(){return B(A1(_9H,_u));});return function(_9Z){return new F(function(){return A1(_9Z,_9Y);});};}else{if(_9L>57){var _a0=new T(function(){return B(A1(_9H,_u));});return function(_a1){return new F(function(){return A1(_a1,_a0);});};}else{return new F(function(){return _9M(_9L-48|0);});}}break;case 16:if(48>_9L){if(97>_9L){if(65>_9L){var _a2=new T(function(){return B(A1(_9H,_u));});return function(_a3){return new F(function(){return A1(_a3,_a2);});};}else{if(_9L>70){var _a4=new T(function(){return B(A1(_9H,_u));});return function(_a5){return new F(function(){return A1(_a5,_a4);});};}else{return new F(function(){return _9M((_9L-65|0)+10|0);});}}}else{if(_9L>102){if(65>_9L){var _a6=new T(function(){return B(A1(_9H,_u));});return function(_a7){return new F(function(){return A1(_a7,_a6);});};}else{if(_9L>70){var _a8=new T(function(){return B(A1(_9H,_u));});return function(_a9){return new F(function(){return A1(_a9,_a8);});};}else{return new F(function(){return _9M((_9L-65|0)+10|0);});}}}else{return new F(function(){return _9M((_9L-97|0)+10|0);});}}}else{if(_9L>57){if(97>_9L){if(65>_9L){var _aa=new T(function(){return B(A1(_9H,_u));});return function(_ab){return new F(function(){return A1(_ab,_aa);});};}else{if(_9L>70){var _ac=new T(function(){return B(A1(_9H,_u));});return function(_ad){return new F(function(){return A1(_ad,_ac);});};}else{return new F(function(){return _9M((_9L-65|0)+10|0);});}}}else{if(_9L>102){if(65>_9L){var _ae=new T(function(){return B(A1(_9H,_u));});return function(_af){return new F(function(){return A1(_af,_ae);});};}else{if(_9L>70){var _ag=new T(function(){return B(A1(_9H,_u));});return function(_ah){return new F(function(){return A1(_ah,_ag);});};}else{return new F(function(){return _9M((_9L-65|0)+10|0);});}}}else{return new F(function(){return _9M((_9L-97|0)+10|0);});}}}else{return new F(function(){return _9M(_9L-48|0);});}}break;default:return E(_9B);}}},_ai=function(_aj){var _ak=E(_aj);if(!_ak._){return new T0(2);}else{return new F(function(){return A1(_9E,_ak);});}};return function(_al){return new F(function(){return A3(_9F,_al,_2q,_ai);});};},_am=16,_an=8,_ao=function(_ap){var _aq=function(_ar){return new F(function(){return A1(_ap,new T1(5,new T2(0,_an,_ar)));});},_as=function(_at){return new F(function(){return A1(_ap,new T1(5,new T2(0,_am,_at)));});},_au=function(_av){switch(E(_av)){case 79:return new T1(1,B(_9C(_an,_aq)));case 88:return new T1(1,B(_9C(_am,_as)));case 111:return new T1(1,B(_9C(_an,_aq)));case 120:return new T1(1,B(_9C(_am,_as)));default:return new T0(2);}};return function(_aw){return (E(_aw)==48)?E(new T1(0,_au)):new T0(2);};},_ax=function(_ay){return new T1(0,B(_ao(_ay)));},_az=function(_aA){return new F(function(){return A1(_aA,_2a);});},_aB=function(_aC){return new F(function(){return A1(_aC,_2a);});},_aD=10,_aE=new T1(0,1),_aF=new T1(0,2147483647),_aG=function(_aH,_aI){while(1){var _aJ=E(_aH);if(!_aJ._){var _aK=_aJ.a,_aL=E(_aI);if(!_aL._){var _aM=_aL.a,_aN=addC(_aK,_aM);if(!E(_aN.b)){return new T1(0,_aN.a);}else{_aH=new T1(1,I_fromInt(_aK));_aI=new T1(1,I_fromInt(_aM));continue;}}else{_aH=new T1(1,I_fromInt(_aK));_aI=_aL;continue;}}else{var _aO=E(_aI);if(!_aO._){_aH=_aJ;_aI=new T1(1,I_fromInt(_aO.a));continue;}else{return new T1(1,I_add(_aJ.a,_aO.a));}}}},_aP=new T(function(){return B(_aG(_aF,_aE));}),_aQ=function(_aR){var _aS=E(_aR);if(!_aS._){var _aT=E(_aS.a);return (_aT==(-2147483648))?E(_aP):new T1(0, -_aT);}else{return new T1(1,I_negate(_aS.a));}},_aU=new T1(0,10),_aV=function(_aW){return new T1(0,_aW);},_aX=function(_aY){return new F(function(){return _aV(E(_aY));});},_aZ=new T(function(){return B(unCStr("this should not happen"));}),_b0=new T(function(){return B(err(_aZ));}),_b1=function(_b2,_b3){while(1){var _b4=E(_b2);if(!_b4._){var _b5=_b4.a,_b6=E(_b3);if(!_b6._){var _b7=_b6.a;if(!(imul(_b5,_b7)|0)){return new T1(0,imul(_b5,_b7)|0);}else{_b2=new T1(1,I_fromInt(_b5));_b3=new T1(1,I_fromInt(_b7));continue;}}else{_b2=new T1(1,I_fromInt(_b5));_b3=_b6;continue;}}else{var _b8=E(_b3);if(!_b8._){_b2=_b4;_b3=new T1(1,I_fromInt(_b8.a));continue;}else{return new T1(1,I_mul(_b4.a,_b8.a));}}}},_b9=function(_ba,_bb){var _bc=E(_bb);if(!_bc._){return __Z;}else{var _bd=E(_bc.b);return (_bd._==0)?E(_b0):new T2(1,B(_aG(B(_b1(_bc.a,_ba)),_bd.a)),new T(function(){return B(_b9(_ba,_bd.b));}));}},_be=new T1(0,0),_bf=function(_bg,_bh,_bi){while(1){var _bj=B((function(_bk,_bl,_bm){var _bn=E(_bm);if(!_bn._){return E(_be);}else{if(!E(_bn.b)._){return E(_bn.a);}else{var _bo=E(_bl);if(_bo<=40){var _bp=function(_bq,_br){while(1){var _bs=E(_br);if(!_bs._){return E(_bq);}else{var _bt=B(_aG(B(_b1(_bq,_bk)),_bs.a));_bq=_bt;_br=_bs.b;continue;}}};return new F(function(){return _bp(_be,_bn);});}else{var _bu=B(_b1(_bk,_bk));if(!(_bo%2)){var _bv=B(_b9(_bk,_bn));_bg=_bu;_bh=quot(_bo+1|0,2);_bi=_bv;return __continue;}else{var _bv=B(_b9(_bk,new T2(1,_be,_bn)));_bg=_bu;_bh=quot(_bo+1|0,2);_bi=_bv;return __continue;}}}}})(_bg,_bh,_bi));if(_bj!=__continue){return _bj;}}},_bw=function(_bx,_by){return new F(function(){return _bf(_bx,new T(function(){return B(_4b(_by,0));},1),B(_5p(_aX,_by)));});},_bz=function(_bA){var _bB=new T(function(){var _bC=new T(function(){var _bD=function(_bE){return new F(function(){return A1(_bA,new T1(1,new T(function(){return B(_bw(_aU,_bE));})));});};return new T1(1,B(_9C(_aD,_bD)));}),_bF=function(_bG){if(E(_bG)==43){var _bH=function(_bI){return new F(function(){return A1(_bA,new T1(1,new T(function(){return B(_bw(_aU,_bI));})));});};return new T1(1,B(_9C(_aD,_bH)));}else{return new T0(2);}},_bJ=function(_bK){if(E(_bK)==45){var _bL=function(_bM){return new F(function(){return A1(_bA,new T1(1,new T(function(){return B(_aQ(B(_bw(_aU,_bM))));})));});};return new T1(1,B(_9C(_aD,_bL)));}else{return new T0(2);}};return B(_7C(B(_7C(new T1(0,_bJ),new T1(0,_bF))),_bC));});return new F(function(){return _7C(new T1(0,function(_bN){return (E(_bN)==101)?E(_bB):new T0(2);}),new T1(0,function(_bO){return (E(_bO)==69)?E(_bB):new T0(2);}));});},_bP=function(_bQ){var _bR=function(_bS){return new F(function(){return A1(_bQ,new T1(1,_bS));});};return function(_bT){return (E(_bT)==46)?new T1(1,B(_9C(_aD,_bR))):new T0(2);};},_bU=function(_bV){return new T1(0,B(_bP(_bV)));},_bW=function(_bX){var _bY=function(_bZ){var _c0=function(_c1){return new T1(1,B(_8V(_bz,_az,function(_c2){return new F(function(){return A1(_bX,new T1(5,new T3(1,_bZ,_c1,_c2)));});})));};return new T1(1,B(_8V(_bU,_aB,_c0)));};return new F(function(){return _9C(_aD,_bY);});},_c3=function(_c4){return new T1(1,B(_bW(_c4)));},_c5=function(_c6,_c7,_c8){while(1){var _c9=E(_c8);if(!_c9._){return false;}else{if(!B(A3(_2A,_c6,_c7,_c9.a))){_c8=_c9.b;continue;}else{return true;}}}},_ca=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_cb=function(_cc){return new F(function(){return _c5(_8r,_cc,_ca);});},_cd=false,_ce=true,_cf=function(_cg){var _ch=new T(function(){return B(A1(_cg,_an));}),_ci=new T(function(){return B(A1(_cg,_am));});return function(_cj){switch(E(_cj)){case 79:return E(_ch);case 88:return E(_ci);case 111:return E(_ch);case 120:return E(_ci);default:return new T0(2);}};},_ck=function(_cl){return new T1(0,B(_cf(_cl)));},_cm=function(_cn){return new F(function(){return A1(_cn,_aD);});},_co=function(_cp,_cq){var _cr=jsShowI(_cp);return new F(function(){return _O(fromJSStr(_cr),_cq);});},_cs=41,_ct=40,_cu=function(_cv,_cw,_cx){if(_cw>=0){return new F(function(){return _co(_cw,_cx);});}else{if(_cv<=6){return new F(function(){return _co(_cw,_cx);});}else{return new T2(1,_ct,new T(function(){var _cy=jsShowI(_cw);return B(_O(fromJSStr(_cy),new T2(1,_cs,_cx)));}));}}},_cz=function(_cA){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_cu(9,_cA,_u));}))));});},_cB=function(_cC){var _cD=E(_cC);if(!_cD._){return E(_cD.a);}else{return new F(function(){return I_toInt(_cD.a);});}},_cE=function(_cF,_cG){var _cH=E(_cF);if(!_cH._){var _cI=_cH.a,_cJ=E(_cG);return (_cJ._==0)?_cI<=_cJ.a:I_compareInt(_cJ.a,_cI)>=0;}else{var _cK=_cH.a,_cL=E(_cG);return (_cL._==0)?I_compareInt(_cK,_cL.a)<=0:I_compare(_cK,_cL.a)<=0;}},_cM=function(_cN){return new T0(2);},_cO=function(_cP){var _cQ=E(_cP);if(!_cQ._){return E(_cM);}else{var _cR=_cQ.a,_cS=E(_cQ.b);if(!_cS._){return E(_cR);}else{var _cT=new T(function(){return B(_cO(_cS));}),_cU=function(_cV){return new F(function(){return _7C(B(A1(_cR,_cV)),new T(function(){return B(A1(_cT,_cV));}));});};return E(_cU);}}},_cW=function(_cX,_cY){var _cZ=function(_d0,_d1,_d2){var _d3=E(_d0);if(!_d3._){return new F(function(){return A1(_d2,_cX);});}else{var _d4=E(_d1);if(!_d4._){return new T0(2);}else{if(E(_d3.a)!=E(_d4.a)){return new T0(2);}else{var _d5=new T(function(){return B(_cZ(_d3.b,_d4.b,_d2));});return new T1(0,function(_d6){return E(_d5);});}}}};return function(_d7){return new F(function(){return _cZ(_cX,_d7,_cY);});};},_d8=new T(function(){return B(unCStr("SO"));}),_d9=14,_da=function(_db){var _dc=new T(function(){return B(A1(_db,_d9));});return new T1(1,B(_cW(_d8,function(_dd){return E(_dc);})));},_de=new T(function(){return B(unCStr("SOH"));}),_df=1,_dg=function(_dh){var _di=new T(function(){return B(A1(_dh,_df));});return new T1(1,B(_cW(_de,function(_dj){return E(_di);})));},_dk=function(_dl){return new T1(1,B(_8V(_dg,_da,_dl)));},_dm=new T(function(){return B(unCStr("NUL"));}),_dn=0,_do=function(_dp){var _dq=new T(function(){return B(A1(_dp,_dn));});return new T1(1,B(_cW(_dm,function(_dr){return E(_dq);})));},_ds=new T(function(){return B(unCStr("STX"));}),_dt=2,_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,_dt));});return new T1(1,B(_cW(_ds,function(_dx){return E(_dw);})));},_dy=new T(function(){return B(unCStr("ETX"));}),_dz=3,_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,_dz));});return new T1(1,B(_cW(_dy,function(_dD){return E(_dC);})));},_dE=new T(function(){return B(unCStr("EOT"));}),_dF=4,_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,_dF));});return new T1(1,B(_cW(_dE,function(_dJ){return E(_dI);})));},_dK=new T(function(){return B(unCStr("ENQ"));}),_dL=5,_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,_dL));});return new T1(1,B(_cW(_dK,function(_dP){return E(_dO);})));},_dQ=new T(function(){return B(unCStr("ACK"));}),_dR=6,_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,_dR));});return new T1(1,B(_cW(_dQ,function(_dV){return E(_dU);})));},_dW=new T(function(){return B(unCStr("BEL"));}),_dX=7,_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,_dX));});return new T1(1,B(_cW(_dW,function(_e1){return E(_e0);})));},_e2=new T(function(){return B(unCStr("BS"));}),_e3=8,_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,_e3));});return new T1(1,B(_cW(_e2,function(_e7){return E(_e6);})));},_e8=new T(function(){return B(unCStr("HT"));}),_e9=9,_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,_e9));});return new T1(1,B(_cW(_e8,function(_ed){return E(_ec);})));},_ee=new T(function(){return B(unCStr("LF"));}),_ef=10,_eg=function(_eh){var _ei=new T(function(){return B(A1(_eh,_ef));});return new T1(1,B(_cW(_ee,function(_ej){return E(_ei);})));},_ek=new T(function(){return B(unCStr("VT"));}),_el=11,_em=function(_en){var _eo=new T(function(){return B(A1(_en,_el));});return new T1(1,B(_cW(_ek,function(_ep){return E(_eo);})));},_eq=new T(function(){return B(unCStr("FF"));}),_er=12,_es=function(_et){var _eu=new T(function(){return B(A1(_et,_er));});return new T1(1,B(_cW(_eq,function(_ev){return E(_eu);})));},_ew=new T(function(){return B(unCStr("CR"));}),_ex=13,_ey=function(_ez){var _eA=new T(function(){return B(A1(_ez,_ex));});return new T1(1,B(_cW(_ew,function(_eB){return E(_eA);})));},_eC=new T(function(){return B(unCStr("SI"));}),_eD=15,_eE=function(_eF){var _eG=new T(function(){return B(A1(_eF,_eD));});return new T1(1,B(_cW(_eC,function(_eH){return E(_eG);})));},_eI=new T(function(){return B(unCStr("DLE"));}),_eJ=16,_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,_eJ));});return new T1(1,B(_cW(_eI,function(_eN){return E(_eM);})));},_eO=new T(function(){return B(unCStr("DC1"));}),_eP=17,_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,_eP));});return new T1(1,B(_cW(_eO,function(_eT){return E(_eS);})));},_eU=new T(function(){return B(unCStr("DC2"));}),_eV=18,_eW=function(_eX){var _eY=new T(function(){return B(A1(_eX,_eV));});return new T1(1,B(_cW(_eU,function(_eZ){return E(_eY);})));},_f0=new T(function(){return B(unCStr("DC3"));}),_f1=19,_f2=function(_f3){var _f4=new T(function(){return B(A1(_f3,_f1));});return new T1(1,B(_cW(_f0,function(_f5){return E(_f4);})));},_f6=new T(function(){return B(unCStr("DC4"));}),_f7=20,_f8=function(_f9){var _fa=new T(function(){return B(A1(_f9,_f7));});return new T1(1,B(_cW(_f6,function(_fb){return E(_fa);})));},_fc=new T(function(){return B(unCStr("NAK"));}),_fd=21,_fe=function(_ff){var _fg=new T(function(){return B(A1(_ff,_fd));});return new T1(1,B(_cW(_fc,function(_fh){return E(_fg);})));},_fi=new T(function(){return B(unCStr("SYN"));}),_fj=22,_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,_fj));});return new T1(1,B(_cW(_fi,function(_fn){return E(_fm);})));},_fo=new T(function(){return B(unCStr("ETB"));}),_fp=23,_fq=function(_fr){var _fs=new T(function(){return B(A1(_fr,_fp));});return new T1(1,B(_cW(_fo,function(_ft){return E(_fs);})));},_fu=new T(function(){return B(unCStr("CAN"));}),_fv=24,_fw=function(_fx){var _fy=new T(function(){return B(A1(_fx,_fv));});return new T1(1,B(_cW(_fu,function(_fz){return E(_fy);})));},_fA=new T(function(){return B(unCStr("EM"));}),_fB=25,_fC=function(_fD){var _fE=new T(function(){return B(A1(_fD,_fB));});return new T1(1,B(_cW(_fA,function(_fF){return E(_fE);})));},_fG=new T(function(){return B(unCStr("SUB"));}),_fH=26,_fI=function(_fJ){var _fK=new T(function(){return B(A1(_fJ,_fH));});return new T1(1,B(_cW(_fG,function(_fL){return E(_fK);})));},_fM=new T(function(){return B(unCStr("ESC"));}),_fN=27,_fO=function(_fP){var _fQ=new T(function(){return B(A1(_fP,_fN));});return new T1(1,B(_cW(_fM,function(_fR){return E(_fQ);})));},_fS=new T(function(){return B(unCStr("FS"));}),_fT=28,_fU=function(_fV){var _fW=new T(function(){return B(A1(_fV,_fT));});return new T1(1,B(_cW(_fS,function(_fX){return E(_fW);})));},_fY=new T(function(){return B(unCStr("GS"));}),_fZ=29,_g0=function(_g1){var _g2=new T(function(){return B(A1(_g1,_fZ));});return new T1(1,B(_cW(_fY,function(_g3){return E(_g2);})));},_g4=new T(function(){return B(unCStr("RS"));}),_g5=30,_g6=function(_g7){var _g8=new T(function(){return B(A1(_g7,_g5));});return new T1(1,B(_cW(_g4,function(_g9){return E(_g8);})));},_ga=new T(function(){return B(unCStr("US"));}),_gb=31,_gc=function(_gd){var _ge=new T(function(){return B(A1(_gd,_gb));});return new T1(1,B(_cW(_ga,function(_gf){return E(_ge);})));},_gg=new T(function(){return B(unCStr("SP"));}),_gh=32,_gi=function(_gj){var _gk=new T(function(){return B(A1(_gj,_gh));});return new T1(1,B(_cW(_gg,function(_gl){return E(_gk);})));},_gm=new T(function(){return B(unCStr("DEL"));}),_gn=127,_go=function(_gp){var _gq=new T(function(){return B(A1(_gp,_gn));});return new T1(1,B(_cW(_gm,function(_gr){return E(_gq);})));},_gs=new T2(1,_go,_u),_gt=new T2(1,_gi,_gs),_gu=new T2(1,_gc,_gt),_gv=new T2(1,_g6,_gu),_gw=new T2(1,_g0,_gv),_gx=new T2(1,_fU,_gw),_gy=new T2(1,_fO,_gx),_gz=new T2(1,_fI,_gy),_gA=new T2(1,_fC,_gz),_gB=new T2(1,_fw,_gA),_gC=new T2(1,_fq,_gB),_gD=new T2(1,_fk,_gC),_gE=new T2(1,_fe,_gD),_gF=new T2(1,_f8,_gE),_gG=new T2(1,_f2,_gF),_gH=new T2(1,_eW,_gG),_gI=new T2(1,_eQ,_gH),_gJ=new T2(1,_eK,_gI),_gK=new T2(1,_eE,_gJ),_gL=new T2(1,_ey,_gK),_gM=new T2(1,_es,_gL),_gN=new T2(1,_em,_gM),_gO=new T2(1,_eg,_gN),_gP=new T2(1,_ea,_gO),_gQ=new T2(1,_e4,_gP),_gR=new T2(1,_dY,_gQ),_gS=new T2(1,_dS,_gR),_gT=new T2(1,_dM,_gS),_gU=new T2(1,_dG,_gT),_gV=new T2(1,_dA,_gU),_gW=new T2(1,_du,_gV),_gX=new T2(1,_do,_gW),_gY=new T2(1,_dk,_gX),_gZ=new T(function(){return B(_cO(_gY));}),_h0=34,_h1=new T1(0,1114111),_h2=92,_h3=39,_h4=function(_h5){var _h6=new T(function(){return B(A1(_h5,_dX));}),_h7=new T(function(){return B(A1(_h5,_e3));}),_h8=new T(function(){return B(A1(_h5,_e9));}),_h9=new T(function(){return B(A1(_h5,_ef));}),_ha=new T(function(){return B(A1(_h5,_el));}),_hb=new T(function(){return B(A1(_h5,_er));}),_hc=new T(function(){return B(A1(_h5,_ex));}),_hd=new T(function(){return B(A1(_h5,_h2));}),_he=new T(function(){return B(A1(_h5,_h3));}),_hf=new T(function(){return B(A1(_h5,_h0));}),_hg=new T(function(){var _hh=function(_hi){var _hj=new T(function(){return B(_aV(E(_hi)));}),_hk=function(_hl){var _hm=B(_bw(_hj,_hl));if(!B(_cE(_hm,_h1))){return new T0(2);}else{return new F(function(){return A1(_h5,new T(function(){var _hn=B(_cB(_hm));if(_hn>>>0>1114111){return B(_cz(_hn));}else{return _hn;}}));});}};return new T1(1,B(_9C(_hi,_hk)));},_ho=new T(function(){var _hp=new T(function(){return B(A1(_h5,_gb));}),_hq=new T(function(){return B(A1(_h5,_g5));}),_hr=new T(function(){return B(A1(_h5,_fZ));}),_hs=new T(function(){return B(A1(_h5,_fT));}),_ht=new T(function(){return B(A1(_h5,_fN));}),_hu=new T(function(){return B(A1(_h5,_fH));}),_hv=new T(function(){return B(A1(_h5,_fB));}),_hw=new T(function(){return B(A1(_h5,_fv));}),_hx=new T(function(){return B(A1(_h5,_fp));}),_hy=new T(function(){return B(A1(_h5,_fj));}),_hz=new T(function(){return B(A1(_h5,_fd));}),_hA=new T(function(){return B(A1(_h5,_f7));}),_hB=new T(function(){return B(A1(_h5,_f1));}),_hC=new T(function(){return B(A1(_h5,_eV));}),_hD=new T(function(){return B(A1(_h5,_eP));}),_hE=new T(function(){return B(A1(_h5,_eJ));}),_hF=new T(function(){return B(A1(_h5,_eD));}),_hG=new T(function(){return B(A1(_h5,_d9));}),_hH=new T(function(){return B(A1(_h5,_dR));}),_hI=new T(function(){return B(A1(_h5,_dL));}),_hJ=new T(function(){return B(A1(_h5,_dF));}),_hK=new T(function(){return B(A1(_h5,_dz));}),_hL=new T(function(){return B(A1(_h5,_dt));}),_hM=new T(function(){return B(A1(_h5,_df));}),_hN=new T(function(){return B(A1(_h5,_dn));}),_hO=function(_hP){switch(E(_hP)){case 64:return E(_hN);case 65:return E(_hM);case 66:return E(_hL);case 67:return E(_hK);case 68:return E(_hJ);case 69:return E(_hI);case 70:return E(_hH);case 71:return E(_h6);case 72:return E(_h7);case 73:return E(_h8);case 74:return E(_h9);case 75:return E(_ha);case 76:return E(_hb);case 77:return E(_hc);case 78:return E(_hG);case 79:return E(_hF);case 80:return E(_hE);case 81:return E(_hD);case 82:return E(_hC);case 83:return E(_hB);case 84:return E(_hA);case 85:return E(_hz);case 86:return E(_hy);case 87:return E(_hx);case 88:return E(_hw);case 89:return E(_hv);case 90:return E(_hu);case 91:return E(_ht);case 92:return E(_hs);case 93:return E(_hr);case 94:return E(_hq);case 95:return E(_hp);default:return new T0(2);}};return B(_7C(new T1(0,function(_hQ){return (E(_hQ)==94)?E(new T1(0,_hO)):new T0(2);}),new T(function(){return B(A1(_gZ,_h5));})));});return B(_7C(new T1(1,B(_8V(_ck,_cm,_hh))),_ho));});return new F(function(){return _7C(new T1(0,function(_hR){switch(E(_hR)){case 34:return E(_hf);case 39:return E(_he);case 92:return E(_hd);case 97:return E(_h6);case 98:return E(_h7);case 102:return E(_hb);case 110:return E(_h9);case 114:return E(_hc);case 116:return E(_h8);case 118:return E(_ha);default:return new T0(2);}}),_hg);});},_hS=function(_hT){return new F(function(){return A1(_hT,_2t);});},_hU=function(_hV){var _hW=E(_hV);if(!_hW._){return E(_hS);}else{var _hX=E(_hW.a),_hY=_hX>>>0,_hZ=new T(function(){return B(_hU(_hW.b));});if(_hY>887){var _i0=u_iswspace(_hX);if(!E(_i0)){return E(_hS);}else{var _i1=function(_i2){var _i3=new T(function(){return B(A1(_hZ,_i2));});return new T1(0,function(_i4){return E(_i3);});};return E(_i1);}}else{var _i5=E(_hY);if(_i5==32){var _i6=function(_i7){var _i8=new T(function(){return B(A1(_hZ,_i7));});return new T1(0,function(_i9){return E(_i8);});};return E(_i6);}else{if(_i5-9>>>0>4){if(E(_i5)==160){var _ia=function(_ib){var _ic=new T(function(){return B(A1(_hZ,_ib));});return new T1(0,function(_id){return E(_ic);});};return E(_ia);}else{return E(_hS);}}else{var _ie=function(_if){var _ig=new T(function(){return B(A1(_hZ,_if));});return new T1(0,function(_ih){return E(_ig);});};return E(_ie);}}}}},_ii=function(_ij){var _ik=new T(function(){return B(_ii(_ij));}),_il=function(_im){return (E(_im)==92)?E(_ik):new T0(2);},_in=function(_io){return E(new T1(0,_il));},_ip=new T1(1,function(_iq){return new F(function(){return A2(_hU,_iq,_in);});}),_ir=new T(function(){return B(_h4(function(_is){return new F(function(){return A1(_ij,new T2(0,_is,_ce));});}));}),_it=function(_iu){var _iv=E(_iu);if(_iv==38){return E(_ik);}else{var _iw=_iv>>>0;if(_iw>887){var _ix=u_iswspace(_iv);return (E(_ix)==0)?new T0(2):E(_ip);}else{var _iy=E(_iw);return (_iy==32)?E(_ip):(_iy-9>>>0>4)?(E(_iy)==160)?E(_ip):new T0(2):E(_ip);}}};return new F(function(){return _7C(new T1(0,function(_iz){return (E(_iz)==92)?E(new T1(0,_it)):new T0(2);}),new T1(0,function(_iA){var _iB=E(_iA);if(E(_iB)==92){return E(_ir);}else{return new F(function(){return A1(_ij,new T2(0,_iB,_cd));});}}));});},_iC=function(_iD,_iE){var _iF=new T(function(){return B(A1(_iE,new T1(1,new T(function(){return B(A1(_iD,_u));}))));}),_iG=function(_iH){var _iI=E(_iH),_iJ=E(_iI.a);if(E(_iJ)==34){if(!E(_iI.b)){return E(_iF);}else{return new F(function(){return _iC(function(_iK){return new F(function(){return A1(_iD,new T2(1,_iJ,_iK));});},_iE);});}}else{return new F(function(){return _iC(function(_iL){return new F(function(){return A1(_iD,new T2(1,_iJ,_iL));});},_iE);});}};return new F(function(){return _ii(_iG);});},_iM=new T(function(){return B(unCStr("_\'"));}),_iN=function(_iO){var _iP=u_iswalnum(_iO);if(!E(_iP)){return new F(function(){return _c5(_8r,_iO,_iM);});}else{return true;}},_iQ=function(_iR){return new F(function(){return _iN(E(_iR));});},_iS=new T(function(){return B(unCStr(",;()[]{}`"));}),_iT=new T(function(){return B(unCStr("=>"));}),_iU=new T2(1,_iT,_u),_iV=new T(function(){return B(unCStr("~"));}),_iW=new T2(1,_iV,_iU),_iX=new T(function(){return B(unCStr("@"));}),_iY=new T2(1,_iX,_iW),_iZ=new T(function(){return B(unCStr("->"));}),_j0=new T2(1,_iZ,_iY),_j1=new T(function(){return B(unCStr("<-"));}),_j2=new T2(1,_j1,_j0),_j3=new T(function(){return B(unCStr("|"));}),_j4=new T2(1,_j3,_j2),_j5=new T(function(){return B(unCStr("\\"));}),_j6=new T2(1,_j5,_j4),_j7=new T(function(){return B(unCStr("="));}),_j8=new T2(1,_j7,_j6),_j9=new T(function(){return B(unCStr("::"));}),_ja=new T2(1,_j9,_j8),_jb=new T(function(){return B(unCStr(".."));}),_jc=new T2(1,_jb,_ja),_jd=function(_je){var _jf=new T(function(){return B(A1(_je,_9z));}),_jg=new T(function(){var _jh=new T(function(){var _ji=function(_jj){var _jk=new T(function(){return B(A1(_je,new T1(0,_jj)));});return new T1(0,function(_jl){return (E(_jl)==39)?E(_jk):new T0(2);});};return B(_h4(_ji));}),_jm=function(_jn){var _jo=E(_jn);switch(E(_jo)){case 39:return new T0(2);case 92:return E(_jh);default:var _jp=new T(function(){return B(A1(_je,new T1(0,_jo)));});return new T1(0,function(_jq){return (E(_jq)==39)?E(_jp):new T0(2);});}},_jr=new T(function(){var _js=new T(function(){return B(_iC(_2q,_je));}),_jt=new T(function(){var _ju=new T(function(){var _jv=new T(function(){var _jw=function(_jx){var _jy=E(_jx),_jz=u_iswalpha(_jy);return (E(_jz)==0)?(E(_jy)==95)?new T1(1,B(_9l(_iQ,function(_jA){return new F(function(){return A1(_je,new T1(3,new T2(1,_jy,_jA)));});}))):new T0(2):new T1(1,B(_9l(_iQ,function(_jB){return new F(function(){return A1(_je,new T1(3,new T2(1,_jy,_jB)));});})));};return B(_7C(new T1(0,_jw),new T(function(){return new T1(1,B(_8V(_ax,_c3,_je)));})));}),_jC=function(_jD){return (!B(_c5(_8r,_jD,_ca)))?new T0(2):new T1(1,B(_9l(_cb,function(_jE){var _jF=new T2(1,_jD,_jE);if(!B(_c5(_8A,_jF,_jc))){return new F(function(){return A1(_je,new T1(4,_jF));});}else{return new F(function(){return A1(_je,new T1(2,_jF));});}})));};return B(_7C(new T1(0,_jC),_jv));});return B(_7C(new T1(0,function(_jG){if(!B(_c5(_8r,_jG,_iS))){return new T0(2);}else{return new F(function(){return A1(_je,new T1(2,new T2(1,_jG,_u)));});}}),_ju));});return B(_7C(new T1(0,function(_jH){return (E(_jH)==34)?E(_js):new T0(2);}),_jt));});return B(_7C(new T1(0,function(_jI){return (E(_jI)==39)?E(new T1(0,_jm)):new T0(2);}),_jr));});return new F(function(){return _7C(new T1(1,function(_jJ){return (E(_jJ)._==0)?E(_jf):new T0(2);}),_jg);});},_jK=0,_jL=function(_jM,_jN){var _jO=new T(function(){var _jP=new T(function(){var _jQ=function(_jR){var _jS=new T(function(){var _jT=new T(function(){return B(A1(_jN,_jR));});return B(_jd(function(_jU){var _jV=E(_jU);return (_jV._==2)?(!B(_8g(_jV.a,_8f)))?new T0(2):E(_jT):new T0(2);}));}),_jW=function(_jX){return E(_jS);};return new T1(1,function(_jY){return new F(function(){return A2(_hU,_jY,_jW);});});};return B(A2(_jM,_jK,_jQ));});return B(_jd(function(_jZ){var _k0=E(_jZ);return (_k0._==2)?(!B(_8g(_k0.a,_8e)))?new T0(2):E(_jP):new T0(2);}));}),_k1=function(_k2){return E(_jO);};return function(_k3){return new F(function(){return A2(_hU,_k3,_k1);});};},_k4=function(_k5,_k6){var _k7=function(_k8){var _k9=new T(function(){return B(A1(_k5,_k8));}),_ka=function(_kb){return new F(function(){return _7C(B(A1(_k9,_kb)),new T(function(){return new T1(1,B(_jL(_k7,_kb)));}));});};return E(_ka);},_kc=new T(function(){return B(A1(_k5,_k6));}),_kd=function(_ke){return new F(function(){return _7C(B(A1(_kc,_ke)),new T(function(){return new T1(1,B(_jL(_k7,_ke)));}));});};return E(_kd);},_kf=function(_kg,_kh){var _ki=function(_kj,_kk){var _kl=function(_km){return new F(function(){return A1(_kk,new T(function(){return  -E(_km);}));});},_kn=new T(function(){return B(_jd(function(_ko){return new F(function(){return A3(_kg,_ko,_kj,_kl);});}));}),_kp=function(_kq){return E(_kn);},_kr=function(_ks){return new F(function(){return A2(_hU,_ks,_kp);});},_kt=new T(function(){return B(_jd(function(_ku){var _kv=E(_ku);if(_kv._==4){var _kw=E(_kv.a);if(!_kw._){return new F(function(){return A3(_kg,_kv,_kj,_kk);});}else{if(E(_kw.a)==45){if(!E(_kw.b)._){return E(new T1(1,_kr));}else{return new F(function(){return A3(_kg,_kv,_kj,_kk);});}}else{return new F(function(){return A3(_kg,_kv,_kj,_kk);});}}}else{return new F(function(){return A3(_kg,_kv,_kj,_kk);});}}));}),_kx=function(_ky){return E(_kt);};return new T1(1,function(_kz){return new F(function(){return A2(_hU,_kz,_kx);});});};return new F(function(){return _k4(_ki,_kh);});},_kA=new T(function(){return 1/0;}),_kB=function(_kC,_kD){return new F(function(){return A1(_kD,_kA);});},_kE=new T(function(){return 0/0;}),_kF=function(_kG,_kH){return new F(function(){return A1(_kH,_kE);});},_kI=new T(function(){return B(unCStr("NaN"));}),_kJ=new T(function(){return B(unCStr("Infinity"));}),_kK=1024,_kL=-1021,_kM=new T(function(){return B(unCStr("base"));}),_kN=new T(function(){return B(unCStr("GHC.Exception"));}),_kO=new T(function(){return B(unCStr("ArithException"));}),_kP=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kM,_kN,_kO),_kQ=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kP,_u,_u),_kR=function(_kS){return E(_kQ);},_kT=function(_kU){var _kV=E(_kU);return new F(function(){return _A(B(_y(_kV.a)),_kR,_kV.b);});},_kW=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_kX=new T(function(){return B(unCStr("denormal"));}),_kY=new T(function(){return B(unCStr("divide by zero"));}),_kZ=new T(function(){return B(unCStr("loss of precision"));}),_l0=new T(function(){return B(unCStr("arithmetic underflow"));}),_l1=new T(function(){return B(unCStr("arithmetic overflow"));}),_l2=function(_l3,_l4){switch(E(_l3)){case 0:return new F(function(){return _O(_l1,_l4);});break;case 1:return new F(function(){return _O(_l0,_l4);});break;case 2:return new F(function(){return _O(_kZ,_l4);});break;case 3:return new F(function(){return _O(_kY,_l4);});break;case 4:return new F(function(){return _O(_kX,_l4);});break;default:return new F(function(){return _O(_kW,_l4);});}},_l5=function(_l6){return new F(function(){return _l2(_l6,_u);});},_l7=function(_l8,_l9,_la){return new F(function(){return _l2(_l9,_la);});},_lb=function(_lc,_ld){return new F(function(){return _1S(_l2,_lc,_ld);});},_le=new T3(0,_l7,_l5,_lb),_lf=new T(function(){return new T5(0,_kR,_le,_lg,_kT,_l5);}),_lg=function(_72){return new T2(0,_lf,_72);},_lh=3,_li=new T(function(){return B(_lg(_lh));}),_lj=new T(function(){return die(_li);}),_lk=function(_ll,_lm){var _ln=E(_ll);if(!_ln._){var _lo=_ln.a,_lp=E(_lm);return (_lp._==0)?_lo==_lp.a:(I_compareInt(_lp.a,_lo)==0)?true:false;}else{var _lq=_ln.a,_lr=E(_lm);return (_lr._==0)?(I_compareInt(_lq,_lr.a)==0)?true:false:(I_compare(_lq,_lr.a)==0)?true:false;}},_ls=new T1(0,0),_lt=function(_lu,_lv){while(1){var _lw=E(_lu);if(!_lw._){var _lx=E(_lw.a);if(_lx==(-2147483648)){_lu=new T1(1,I_fromInt(-2147483648));continue;}else{var _ly=E(_lv);if(!_ly._){return new T1(0,_lx%_ly.a);}else{_lu=new T1(1,I_fromInt(_lx));_lv=_ly;continue;}}}else{var _lz=_lw.a,_lA=E(_lv);return (_lA._==0)?new T1(1,I_rem(_lz,I_fromInt(_lA.a))):new T1(1,I_rem(_lz,_lA.a));}}},_lB=function(_lC,_lD){if(!B(_lk(_lD,_ls))){return new F(function(){return _lt(_lC,_lD);});}else{return E(_lj);}},_lE=function(_lF,_lG){while(1){if(!B(_lk(_lG,_ls))){var _lH=_lG,_lI=B(_lB(_lF,_lG));_lF=_lH;_lG=_lI;continue;}else{return E(_lF);}}},_lJ=function(_lK){var _lL=E(_lK);if(!_lL._){var _lM=E(_lL.a);return (_lM==(-2147483648))?E(_aP):(_lM<0)?new T1(0, -_lM):E(_lL);}else{var _lN=_lL.a;return (I_compareInt(_lN,0)>=0)?E(_lL):new T1(1,I_negate(_lN));}},_lO=function(_lP,_lQ){while(1){var _lR=E(_lP);if(!_lR._){var _lS=E(_lR.a);if(_lS==(-2147483648)){_lP=new T1(1,I_fromInt(-2147483648));continue;}else{var _lT=E(_lQ);if(!_lT._){return new T1(0,quot(_lS,_lT.a));}else{_lP=new T1(1,I_fromInt(_lS));_lQ=_lT;continue;}}}else{var _lU=_lR.a,_lV=E(_lQ);return (_lV._==0)?new T1(0,I_toInt(I_quot(_lU,I_fromInt(_lV.a)))):new T1(1,I_quot(_lU,_lV.a));}}},_lW=5,_lX=new T(function(){return B(_lg(_lW));}),_lY=new T(function(){return die(_lX);}),_lZ=function(_m0,_m1){if(!B(_lk(_m1,_ls))){var _m2=B(_lE(B(_lJ(_m0)),B(_lJ(_m1))));return (!B(_lk(_m2,_ls)))?new T2(0,B(_lO(_m0,_m2)),B(_lO(_m1,_m2))):E(_lj);}else{return E(_lY);}},_m3=new T1(0,1),_m4=new T(function(){return B(unCStr("Negative exponent"));}),_m5=new T(function(){return B(err(_m4));}),_m6=new T1(0,2),_m7=new T(function(){return B(_lk(_m6,_ls));}),_m8=function(_m9,_ma){while(1){var _mb=E(_m9);if(!_mb._){var _mc=_mb.a,_md=E(_ma);if(!_md._){var _me=_md.a,_mf=subC(_mc,_me);if(!E(_mf.b)){return new T1(0,_mf.a);}else{_m9=new T1(1,I_fromInt(_mc));_ma=new T1(1,I_fromInt(_me));continue;}}else{_m9=new T1(1,I_fromInt(_mc));_ma=_md;continue;}}else{var _mg=E(_ma);if(!_mg._){_m9=_mb;_ma=new T1(1,I_fromInt(_mg.a));continue;}else{return new T1(1,I_sub(_mb.a,_mg.a));}}}},_mh=function(_mi,_mj,_mk){while(1){if(!E(_m7)){if(!B(_lk(B(_lt(_mj,_m6)),_ls))){if(!B(_lk(_mj,_m3))){var _ml=B(_b1(_mi,_mi)),_mm=B(_lO(B(_m8(_mj,_m3)),_m6)),_mn=B(_b1(_mi,_mk));_mi=_ml;_mj=_mm;_mk=_mn;continue;}else{return new F(function(){return _b1(_mi,_mk);});}}else{var _ml=B(_b1(_mi,_mi)),_mm=B(_lO(_mj,_m6));_mi=_ml;_mj=_mm;continue;}}else{return E(_lj);}}},_mo=function(_mp,_mq){while(1){if(!E(_m7)){if(!B(_lk(B(_lt(_mq,_m6)),_ls))){if(!B(_lk(_mq,_m3))){return new F(function(){return _mh(B(_b1(_mp,_mp)),B(_lO(B(_m8(_mq,_m3)),_m6)),_mp);});}else{return E(_mp);}}else{var _mr=B(_b1(_mp,_mp)),_ms=B(_lO(_mq,_m6));_mp=_mr;_mq=_ms;continue;}}else{return E(_lj);}}},_mt=function(_mu,_mv){var _mw=E(_mu);if(!_mw._){var _mx=_mw.a,_my=E(_mv);return (_my._==0)?_mx<_my.a:I_compareInt(_my.a,_mx)>0;}else{var _mz=_mw.a,_mA=E(_mv);return (_mA._==0)?I_compareInt(_mz,_mA.a)<0:I_compare(_mz,_mA.a)<0;}},_mB=function(_mC,_mD){if(!B(_mt(_mD,_ls))){if(!B(_lk(_mD,_ls))){return new F(function(){return _mo(_mC,_mD);});}else{return E(_m3);}}else{return E(_m5);}},_mE=new T1(0,1),_mF=new T1(0,0),_mG=new T1(0,-1),_mH=function(_mI){var _mJ=E(_mI);if(!_mJ._){var _mK=_mJ.a;return (_mK>=0)?(E(_mK)==0)?E(_mF):E(_aE):E(_mG);}else{var _mL=I_compareInt(_mJ.a,0);return (_mL<=0)?(E(_mL)==0)?E(_mF):E(_mG):E(_aE);}},_mM=function(_mN,_mO,_mP){while(1){var _mQ=E(_mP);if(!_mQ._){if(!B(_mt(_mN,_be))){return new T2(0,B(_b1(_mO,B(_mB(_aU,_mN)))),_m3);}else{var _mR=B(_mB(_aU,B(_aQ(_mN))));return new F(function(){return _lZ(B(_b1(_mO,B(_mH(_mR)))),B(_lJ(_mR)));});}}else{var _mS=B(_m8(_mN,_mE)),_mT=B(_aG(B(_b1(_mO,_aU)),B(_aV(E(_mQ.a)))));_mN=_mS;_mO=_mT;_mP=_mQ.b;continue;}}},_mU=function(_mV,_mW){var _mX=E(_mV);if(!_mX._){var _mY=_mX.a,_mZ=E(_mW);return (_mZ._==0)?_mY>=_mZ.a:I_compareInt(_mZ.a,_mY)<=0;}else{var _n0=_mX.a,_n1=E(_mW);return (_n1._==0)?I_compareInt(_n0,_n1.a)>=0:I_compare(_n0,_n1.a)>=0;}},_n2=function(_n3){var _n4=E(_n3);if(!_n4._){var _n5=_n4.b;return new F(function(){return _lZ(B(_b1(B(_bf(new T(function(){return B(_aV(E(_n4.a)));}),new T(function(){return B(_4b(_n5,0));},1),B(_5p(_aX,_n5)))),_mE)),_mE);});}else{var _n6=_n4.a,_n7=_n4.c,_n8=E(_n4.b);if(!_n8._){var _n9=E(_n7);if(!_n9._){return new F(function(){return _lZ(B(_b1(B(_bw(_aU,_n6)),_mE)),_mE);});}else{var _na=_n9.a;if(!B(_mU(_na,_be))){var _nb=B(_mB(_aU,B(_aQ(_na))));return new F(function(){return _lZ(B(_b1(B(_bw(_aU,_n6)),B(_mH(_nb)))),B(_lJ(_nb)));});}else{return new F(function(){return _lZ(B(_b1(B(_b1(B(_bw(_aU,_n6)),B(_mB(_aU,_na)))),_mE)),_mE);});}}}else{var _nc=_n8.a,_nd=E(_n7);if(!_nd._){return new F(function(){return _mM(_be,B(_bw(_aU,_n6)),_nc);});}else{return new F(function(){return _mM(_nd.a,B(_bw(_aU,_n6)),_nc);});}}}},_ne=function(_nf,_ng){while(1){var _nh=E(_ng);if(!_nh._){return __Z;}else{if(!B(A1(_nf,_nh.a))){return E(_nh);}else{_ng=_nh.b;continue;}}}},_ni=function(_nj,_nk){var _nl=E(_nj);if(!_nl._){var _nm=_nl.a,_nn=E(_nk);return (_nn._==0)?_nm>_nn.a:I_compareInt(_nn.a,_nm)<0;}else{var _no=_nl.a,_np=E(_nk);return (_np._==0)?I_compareInt(_no,_np.a)>0:I_compare(_no,_np.a)>0;}},_nq=0,_nr=function(_ns,_nt){return E(_ns)==E(_nt);},_nu=function(_nv){return new F(function(){return _nr(_nq,_nv);});},_nw=new T2(0,E(_be),E(_m3)),_nx=new T1(1,_nw),_ny=new T1(0,-2147483648),_nz=new T1(0,2147483647),_nA=function(_nB,_nC,_nD){var _nE=E(_nD);if(!_nE._){return new T1(1,new T(function(){var _nF=B(_n2(_nE));return new T2(0,E(_nF.a),E(_nF.b));}));}else{var _nG=E(_nE.c);if(!_nG._){return new T1(1,new T(function(){var _nH=B(_n2(_nE));return new T2(0,E(_nH.a),E(_nH.b));}));}else{var _nI=_nG.a;if(!B(_ni(_nI,_nz))){if(!B(_mt(_nI,_ny))){var _nJ=function(_nK){var _nL=_nK+B(_cB(_nI))|0;return (_nL<=(E(_nC)+3|0))?(_nL>=(E(_nB)-3|0))?new T1(1,new T(function(){var _nM=B(_n2(_nE));return new T2(0,E(_nM.a),E(_nM.b));})):E(_nx):__Z;},_nN=B(_ne(_nu,_nE.a));if(!_nN._){var _nO=E(_nE.b);if(!_nO._){return E(_nx);}else{var _nP=B(_73(_nu,_nO.a));if(!E(_nP.b)._){return E(_nx);}else{return new F(function(){return _nJ( -B(_4b(_nP.a,0)));});}}}else{return new F(function(){return _nJ(B(_4b(_nN,0)));});}}else{return __Z;}}else{return __Z;}}}},_nQ=function(_nR,_nS){return new T0(2);},_nT=new T1(0,1),_nU=function(_nV,_nW){var _nX=E(_nV);if(!_nX._){var _nY=_nX.a,_nZ=E(_nW);if(!_nZ._){var _o0=_nZ.a;return (_nY!=_o0)?(_nY>_o0)?2:0:1;}else{var _o1=I_compareInt(_nZ.a,_nY);return (_o1<=0)?(_o1>=0)?1:2:0;}}else{var _o2=_nX.a,_o3=E(_nW);if(!_o3._){var _o4=I_compareInt(_o2,_o3.a);return (_o4>=0)?(_o4<=0)?1:2:0;}else{var _o5=I_compare(_o2,_o3.a);return (_o5>=0)?(_o5<=0)?1:2:0;}}},_o6=function(_o7,_o8){var _o9=E(_o7);return (_o9._==0)?_o9.a*Math.pow(2,_o8):I_toNumber(_o9.a)*Math.pow(2,_o8);},_oa=function(_ob,_oc){while(1){var _od=E(_ob);if(!_od._){var _oe=E(_od.a);if(_oe==(-2147483648)){_ob=new T1(1,I_fromInt(-2147483648));continue;}else{var _of=E(_oc);if(!_of._){var _og=_of.a;return new T2(0,new T1(0,quot(_oe,_og)),new T1(0,_oe%_og));}else{_ob=new T1(1,I_fromInt(_oe));_oc=_of;continue;}}}else{var _oh=E(_oc);if(!_oh._){_ob=_od;_oc=new T1(1,I_fromInt(_oh.a));continue;}else{var _oi=I_quotRem(_od.a,_oh.a);return new T2(0,new T1(1,_oi.a),new T1(1,_oi.b));}}}},_oj=new T1(0,0),_ok=function(_ol,_om){while(1){var _on=E(_ol);if(!_on._){_ol=new T1(1,I_fromInt(_on.a));continue;}else{return new T1(1,I_shiftLeft(_on.a,_om));}}},_oo=function(_op,_oq,_or){if(!B(_lk(_or,_oj))){var _os=B(_oa(_oq,_or)),_ot=_os.a;switch(B(_nU(B(_ok(_os.b,1)),_or))){case 0:return new F(function(){return _o6(_ot,_op);});break;case 1:if(!(B(_cB(_ot))&1)){return new F(function(){return _o6(_ot,_op);});}else{return new F(function(){return _o6(B(_aG(_ot,_nT)),_op);});}break;default:return new F(function(){return _o6(B(_aG(_ot,_nT)),_op);});}}else{return E(_lj);}},_ou=function(_ov){var _ow=function(_ox,_oy){while(1){if(!B(_mt(_ox,_ov))){if(!B(_ni(_ox,_ov))){if(!B(_lk(_ox,_ov))){return new F(function(){return _7p("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_oy);}}else{return _oy-1|0;}}else{var _oz=B(_ok(_ox,1)),_oA=_oy+1|0;_ox=_oz;_oy=_oA;continue;}}};return new F(function(){return _ow(_aE,0);});},_oB=function(_oC){var _oD=E(_oC);if(!_oD._){var _oE=_oD.a>>>0;if(!_oE){return -1;}else{var _oF=function(_oG,_oH){while(1){if(_oG>=_oE){if(_oG<=_oE){if(_oG!=_oE){return new F(function(){return _7p("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_oH);}}else{return _oH-1|0;}}else{var _oI=imul(_oG,2)>>>0,_oJ=_oH+1|0;_oG=_oI;_oH=_oJ;continue;}}};return new F(function(){return _oF(1,0);});}}else{return new F(function(){return _ou(_oD);});}},_oK=function(_oL){var _oM=E(_oL);if(!_oM._){var _oN=_oM.a>>>0;if(!_oN){return new T2(0,-1,0);}else{var _oO=function(_oP,_oQ){while(1){if(_oP>=_oN){if(_oP<=_oN){if(_oP!=_oN){return new F(function(){return _7p("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_oQ);}}else{return _oQ-1|0;}}else{var _oR=imul(_oP,2)>>>0,_oS=_oQ+1|0;_oP=_oR;_oQ=_oS;continue;}}};return new T2(0,B(_oO(1,0)),(_oN&_oN-1>>>0)>>>0&4294967295);}}else{var _oT=_oM.a;return new T2(0,B(_oB(_oM)),I_compareInt(I_and(_oT,I_sub(_oT,I_fromInt(1))),0));}},_oU=function(_oV,_oW){while(1){var _oX=E(_oV);if(!_oX._){var _oY=_oX.a,_oZ=E(_oW);if(!_oZ._){return new T1(0,(_oY>>>0&_oZ.a>>>0)>>>0&4294967295);}else{_oV=new T1(1,I_fromInt(_oY));_oW=_oZ;continue;}}else{var _p0=E(_oW);if(!_p0._){_oV=_oX;_oW=new T1(1,I_fromInt(_p0.a));continue;}else{return new T1(1,I_and(_oX.a,_p0.a));}}}},_p1=new T1(0,2),_p2=function(_p3,_p4){var _p5=E(_p3);if(!_p5._){var _p6=(_p5.a>>>0&(2<<_p4>>>0)-1>>>0)>>>0,_p7=1<<_p4>>>0;return (_p7<=_p6)?(_p7>=_p6)?1:2:0;}else{var _p8=B(_oU(_p5,B(_m8(B(_ok(_p1,_p4)),_aE)))),_p9=B(_ok(_aE,_p4));return (!B(_ni(_p9,_p8)))?(!B(_mt(_p9,_p8)))?1:2:0;}},_pa=function(_pb,_pc){while(1){var _pd=E(_pb);if(!_pd._){_pb=new T1(1,I_fromInt(_pd.a));continue;}else{return new T1(1,I_shiftRight(_pd.a,_pc));}}},_pe=function(_pf,_pg,_ph,_pi){var _pj=B(_oK(_pi)),_pk=_pj.a;if(!E(_pj.b)){var _pl=B(_oB(_ph));if(_pl<((_pk+_pf|0)-1|0)){var _pm=_pk+(_pf-_pg|0)|0;if(_pm>0){if(_pm>_pl){if(_pm<=(_pl+1|0)){if(!E(B(_oK(_ph)).b)){return 0;}else{return new F(function(){return _o6(_nT,_pf-_pg|0);});}}else{return 0;}}else{var _pn=B(_pa(_ph,_pm));switch(B(_p2(_ph,_pm-1|0))){case 0:return new F(function(){return _o6(_pn,_pf-_pg|0);});break;case 1:if(!(B(_cB(_pn))&1)){return new F(function(){return _o6(_pn,_pf-_pg|0);});}else{return new F(function(){return _o6(B(_aG(_pn,_nT)),_pf-_pg|0);});}break;default:return new F(function(){return _o6(B(_aG(_pn,_nT)),_pf-_pg|0);});}}}else{return new F(function(){return _o6(_ph,(_pf-_pg|0)-_pm|0);});}}else{if(_pl>=_pg){var _po=B(_pa(_ph,(_pl+1|0)-_pg|0));switch(B(_p2(_ph,_pl-_pg|0))){case 0:return new F(function(){return _o6(_po,((_pl-_pk|0)+1|0)-_pg|0);});break;case 2:return new F(function(){return _o6(B(_aG(_po,_nT)),((_pl-_pk|0)+1|0)-_pg|0);});break;default:if(!(B(_cB(_po))&1)){return new F(function(){return _o6(_po,((_pl-_pk|0)+1|0)-_pg|0);});}else{return new F(function(){return _o6(B(_aG(_po,_nT)),((_pl-_pk|0)+1|0)-_pg|0);});}}}else{return new F(function(){return _o6(_ph, -_pk);});}}}else{var _pp=B(_oB(_ph))-_pk|0,_pq=function(_pr){var _ps=function(_pt,_pu){if(!B(_cE(B(_ok(_pu,_pg)),_pt))){return new F(function(){return _oo(_pr-_pg|0,_pt,_pu);});}else{return new F(function(){return _oo((_pr-_pg|0)+1|0,_pt,B(_ok(_pu,1)));});}};if(_pr>=_pg){if(_pr!=_pg){return new F(function(){return _ps(_ph,new T(function(){return B(_ok(_pi,_pr-_pg|0));}));});}else{return new F(function(){return _ps(_ph,_pi);});}}else{return new F(function(){return _ps(new T(function(){return B(_ok(_ph,_pg-_pr|0));}),_pi);});}};if(_pf>_pp){return new F(function(){return _pq(_pf);});}else{return new F(function(){return _pq(_pp);});}}},_pv=new T(function(){return 0/0;}),_pw=new T(function(){return -1/0;}),_px=new T(function(){return 1/0;}),_py=0,_pz=function(_pA,_pB){if(!B(_lk(_pB,_oj))){if(!B(_lk(_pA,_oj))){if(!B(_mt(_pA,_oj))){return new F(function(){return _pe(-1021,53,_pA,_pB);});}else{return  -B(_pe(-1021,53,B(_aQ(_pA)),_pB));}}else{return E(_py);}}else{return (!B(_lk(_pA,_oj)))?(!B(_mt(_pA,_oj)))?E(_px):E(_pw):E(_pv);}},_pC=function(_pD){var _pE=E(_pD);switch(_pE._){case 3:var _pF=_pE.a;return (!B(_8g(_pF,_kJ)))?(!B(_8g(_pF,_kI)))?E(_nQ):E(_kF):E(_kB);case 5:var _pG=B(_nA(_kL,_kK,_pE.a));if(!_pG._){return E(_kB);}else{var _pH=new T(function(){var _pI=E(_pG.a);return B(_pz(_pI.a,_pI.b));});return function(_pJ,_pK){return new F(function(){return A1(_pK,_pH);});};}break;default:return E(_nQ);}},_pL=function(_pM){var _pN=function(_pO){return E(new T2(3,_pM,_8M));};return new T1(1,function(_pP){return new F(function(){return A2(_hU,_pP,_pN);});});},_pQ=new T(function(){return B(A3(_kf,_pC,_jK,_pL));}),_pR=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_pS=function(_pT){return new F(function(){return _70(new T1(0,new T(function(){return B(_7e(_pT,_pR));})),_6K);});},_pU=new T(function(){return B(_pS("SMHI.hs:27:5-38|Str json"));}),_pV="value",_pW=function(_pX){while(1){var _pY=B((function(_pZ){var _q0=E(_pZ);if(!_q0._){return __Z;}else{var _q1=_q0.b,_q2=E(_q0.a);if(!E(_q2.b)._){return new T2(1,_q2.a,new T(function(){return B(_pW(_q1));}));}else{_pX=_q1;return __continue;}}})(_pX));if(_pY!=__continue){return _pY;}}},_q3=function(_q4,_q5){var _q6=E(_q5);if(!_q6._){return __Z;}else{var _q7=new T(function(){return B(_q3(new T(function(){return E(_q4)+1;}),_q6.b));}),_q8=new T(function(){var _q9=B(_pW(B(_7s(_pQ,new T(function(){var _qa=B(_2T(_q6.a,_pV));if(_qa._==1){return fromJSStr(_qa.a);}else{return E(_pU);}})))));if(!_q9._){return E(_6t);}else{if(!E(_q9.b)._){return E(_q9.a);}else{return E(_6v);}}});return new T2(1,new T2(0,_q4,_q8),_q7);}},_qb=new T(function(){return B(unCStr("http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/71420/period/latest-"));}),_qc=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_qd=function(_qe,_qf){var _qg=function(_){var _qh=__app1(E(_qc),E(_qf)),_qi=__eq(_qh,E(_5L));return (E(_qi)==0)?new T1(1,_qh):_2a;};return new F(function(){return A2(_5M,_qe,_qg);});},_qj=new T(function(){return eval("(function(s){var x = eval(s);return (typeof x === \'undefined\') ? \'undefined\' : x.toString();})");}),_qk=function(_ql){var _qm=u_towlower(E(_ql));if(_qm>>>0>1114111){return new F(function(){return _cz(_qm);});}else{return _qm;}},_qn=new T(function(){return B(unCStr("/data.json"));}),_qo=function(_qp){var _qq=E(_qp);return (_qq._==0)?E(_qn):new T2(1,new T(function(){return B(_qk(_qq.a));}),new T(function(){return B(_qo(_qq.b));}));},_qr=function(_qs,_qt){while(1){var _qu=E(_qs);if(!_qu._){return E(_qt);}else{_qs=_qu.b;_qt=_qu.a;continue;}}},_qv=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_qw=function(_qx,_qy,_qz){var _qA=new T(function(){return toJSStr(E(_qz));});return function(_qB,_){var _qC=__app4(E(_qv),E(_qB),E(_qA),E(_qx),E(_qy));return new F(function(){return _3V(_);});};},_qD=10,_qE=40,_qF=new T(function(){return B(unCStr("30\u00b0 C"));}),_qG=new T(function(){return B(_qw(_qD,_qE,_qF));}),_qH=new T(function(){return B(unCStr("last"));}),_qI=new T(function(){return B(_6n(_qH));}),_qJ=new T3(0,128,128,128),_qK=",",_qL="rgba(",_qM=new T(function(){return toJSStr(_u);}),_qN="rgb(",_qO=")",_qP=new T2(1,_qO,_u),_qQ=function(_qR){var _qS=E(_qR);if(!_qS._){var _qT=jsCat(new T2(1,_qN,new T2(1,new T(function(){return String(_qS.a);}),new T2(1,_qK,new T2(1,new T(function(){return String(_qS.b);}),new T2(1,_qK,new T2(1,new T(function(){return String(_qS.c);}),_qP)))))),E(_qM));return E(_qT);}else{var _qU=jsCat(new T2(1,_qL,new T2(1,new T(function(){return String(_qS.a);}),new T2(1,_qK,new T2(1,new T(function(){return String(_qS.b);}),new T2(1,_qK,new T2(1,new T(function(){return String(_qS.c);}),new T2(1,_qK,new T2(1,new T(function(){return String(_qS.d);}),_qP)))))))),E(_qM));return E(_qU);}},_qV="fillStyle",_qW=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_qX=function(_qY){var _qZ=new T(function(){return B(_qQ(_qY));});return function(_r0,_){var _r1=__app3(E(_qW),E(_r0),E(_qV),E(_qZ));return new F(function(){return _3V(_);});};},_r2=new T(function(){return B(_qX(_qJ));}),_r3=new T(function(){return B(unCStr("Pattern match failure in do expression at SMHI.hs:41:11-21"));}),_r4=new T6(0,_2a,_2b,_u,_r3,_2a,_2a),_r5=new T(function(){return B(_1D(_r4));}),_r6=new T(function(){return B(unCStr("\").innerHTML = \"Hourly Temparature in Gothenburg from \" + start.toDateString() + \" \" + start.toTimeString() + \" to \" + end.toDateString() + \" \" + end.toTimeString();"));}),_r7=new T(function(){return B(_pS("SMHI.hs:42:15-60|Arr dataPoints"));}),_r8=new T(function(){return B(_pS("SMHI.hs:48:15-50|Num tend"));}),_r9="date",_ra=new T(function(){return B(_pS("SMHI.hs:45:15-54|Num tstart"));}),_rb=new T3(0,0,0,0),_rc="strokeStyle",_rd=function(_re){var _rf=new T(function(){return B(_qQ(_re));});return function(_rg,_){var _rh=__app3(E(_qW),E(_rg),E(_rc),E(_rf));return new F(function(){return _3V(_);});};},_ri=new T(function(){return B(_rd(_rb));}),_rj=new T(function(){return B(_qX(_rb));}),_rk=290,_rl=new T(function(){return B(unCStr("-20\u00b0 C"));}),_rm=new T(function(){return B(_qw(_qD,_rk,_rl));}),_rn=240,_ro=new T(function(){return B(unCStr("-10\u00b0 C"));}),_rp=new T(function(){return B(_qw(_qD,_rn,_ro));}),_rq=190,_rr=new T(function(){return B(unCStr("0\u00b0 C"));}),_rs=new T(function(){return B(_qw(_qD,_rq,_rr));}),_rt=140,_ru=new T(function(){return B(unCStr("10\u00b0 C"));}),_rv=new T(function(){return B(_qw(_qD,_rt,_ru));}),_rw=90,_rx=new T(function(){return B(unCStr("20\u00b0 C"));}),_ry=new T(function(){return B(_qw(_qD,_rw,_rx));}),_rz=300,_rA=function(_rB,_rC,_rD,_){while(1){var _rE=B((function(_rF,_rG,_rH,_){var _rI=E(_rF);if(!_rI._){return _2t;}else{var _rJ=E(_rI.a),_rK=_rJ.a,_rL=new T(function(){return E(_rK)*E(_rG);}),_rM=new T(function(){return (E(_rK)+1)*E(_rG);}),_rN=new T(function(){return 200-E(_rJ.b)*5;}),_rO=B(_4y(new T2(1,new T2(0,_rL,_rz),new T2(1,new T2(0,_rM,_rz),new T2(1,new T2(0,_rM,_rN),new T2(1,new T2(0,_rL,_rN),new T2(1,new T2(0,_rL,_rz),_u))))),_rH,_)),_rP=_rG,_rQ=_rH;_rB=_rI.b;_rC=_rP;_rD=_rQ;return __continue;}})(_rB,_rC,_rD,_));if(_rE!=__continue){return _rE;}}},_rR=new T(function(){return eval("(function(x){console.log(x);})");}),_rS=function(_rT,_rU){var _rV=function(_){var _rW=__app1(E(_rR),toJSStr(E(_rU)));return new F(function(){return _3V(_);});};return new F(function(){return A2(_5M,_rT,_rV);});},_rX=function(_rY,_){var _rZ=new T(function(){return B(_O(_qb,new T(function(){return B(_qo(_rY));},1)));}),_s0=B(A3(_rS,_2s,_rZ,_)),_s1=new T(function(){return toJSStr(B(unAppCStr("canvas",_rY)));}),_s2=new T(function(){return B(unAppCStr("); document.getElementById(\"title",new T(function(){return B(_O(_rY,_r6));})));}),_s3=function(_s4,_){var _s5=E(_s4);if(!_s5._){return _2t;}else{var _s6=B(A3(_qd,_2s,_s1,_)),_s7=function(_,_s8){var _s9=E(_s8);if(!_s9._){return new F(function(){return die(_r5);});}else{var _sa=new T(function(){return B(_4s(800,new T(function(){var _sb=B(_2T(_s5.a,_pV));if(_sb._==3){return E(_sb.a);}else{return E(_r7);}},1)));}),_sc=new T(function(){var _sd=E(_sa);if(!_sd._){return E(_6q);}else{var _se=B(_2T(_sd.a,_r9));if(!_se._){var _sf=jsShow(_se.a),_sg=new T(function(){return B(unAppCStr(");var end = new Date (",new T(function(){var _sh=B(_2T(B(_qr(_sd,_qI)),_r9));if(!_sh._){var _si=jsShow(_sh.a);return B(_O(fromJSStr(_si),_s2));}else{return E(_r8);}})));},1);return B(_O(fromJSStr(_sf),_sg));}else{return E(_ra);}}}),_sj=__app1(E(_qj),toJSStr(B(unAppCStr("var start = new Date(",_sc)))),_sk=E(_s9.a),_sl=_sk.a,_sm=__app1(E(_6r),_sk.b),_sn=B(A2(_r2,_sl,_)),_so=new T(function(){return B(_q3(_4S,_sa));}),_sp=new T(function(){return 800/B(_4b(_so,0));}),_sq=B(_3Y(function(_sr,_){return new F(function(){return _rA(_so,_sp,_sr,_);});},_sl,_)),_ss=B(A2(_ri,_sl,_)),_st=B(_45(_5f,_sl,_)),_su=B(A2(_rj,_sl,_)),_sv=B(A2(_rm,_sl,_)),_sw=B(A2(_rp,_sl,_)),_sx=B(A2(_rs,_sl,_)),_sy=B(A2(_rv,_sl,_)),_sz=B(A2(_ry,_sl,_));return new F(function(){return A2(_qG,_sl,_);});}},_sA=E(_s6);if(!_sA._){return new F(function(){return _s7(_,_2a);});}else{var _sB=E(_sA.a),_sC=__app1(E(_2Z),_sB);if(!_sC){return new F(function(){return _s7(_,_2a);});}else{var _sD=__app1(E(_2Y),_sB);return new F(function(){return _s7(_,new T1(1,new T2(0,_sD,_sB)));});}}}};return new F(function(){return A(_5S,[_2s,_39,_39,_3U,_4v,_rZ,_u,_s3,_]);});},_sE=function(_){var _sF=B(A3(_rS,_2s,_2x,_)),_sG=B(_rX(_2w,_)),_sH=B(_rX(_2v,_)),_sI=B(_rX(_2u,_));return _2t;},_sJ=function(_){return new F(function(){return _sE(_);});};
var hasteMain = function() {B(A(_sJ, [0]));};window.onload = hasteMain;