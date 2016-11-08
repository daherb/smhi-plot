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

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4,_){var _5=B(A1(_3,_)),_6=B(A1(_4,_));return _5;},_7=function(_8,_9,_){var _a=B(A1(_8,_)),_b=B(A1(_9,_));return new T(function(){return B(A1(_a,_b));});},_c=function(_d,_e,_){var _f=B(A1(_e,_));return _d;},_g=function(_h,_i,_){var _j=B(A1(_i,_));return new T(function(){return B(A1(_h,_j));});},_k=new T2(0,_g,_c),_l=function(_m,_){return _m;},_n=function(_o,_p,_){var _q=B(A1(_o,_));return new F(function(){return A1(_p,_);});},_r=new T5(0,_k,_l,_7,_n,_2),_s=new T(function(){return B(unCStr("base"));}),_t=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_u=new T(function(){return B(unCStr("IOException"));}),_v=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_s,_t,_u),_w=__Z,_x=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_v,_w,_w),_y=function(_z){return E(_x);},_A=function(_B){return E(E(_B).a);},_C=function(_D,_E,_F){var _G=B(A1(_D,_)),_H=B(A1(_E,_)),_I=hs_eqWord64(_G.a,_H.a);if(!_I){return __Z;}else{var _J=hs_eqWord64(_G.b,_H.b);return (!_J)?__Z:new T1(1,_F);}},_K=function(_L){var _M=E(_L);return new F(function(){return _C(B(_A(_M.a)),_y,_M.b);});},_N=new T(function(){return B(unCStr(": "));}),_O=new T(function(){return B(unCStr(")"));}),_P=new T(function(){return B(unCStr(" ("));}),_Q=function(_R,_S){var _T=E(_R);return (_T._==0)?E(_S):new T2(1,_T.a,new T(function(){return B(_Q(_T.b,_S));}));},_U=new T(function(){return B(unCStr("interrupted"));}),_V=new T(function(){return B(unCStr("system error"));}),_W=new T(function(){return B(unCStr("unsatisified constraints"));}),_X=new T(function(){return B(unCStr("user error"));}),_Y=new T(function(){return B(unCStr("permission denied"));}),_Z=new T(function(){return B(unCStr("illegal operation"));}),_10=new T(function(){return B(unCStr("end of file"));}),_11=new T(function(){return B(unCStr("resource exhausted"));}),_12=new T(function(){return B(unCStr("resource busy"));}),_13=new T(function(){return B(unCStr("does not exist"));}),_14=new T(function(){return B(unCStr("already exists"));}),_15=new T(function(){return B(unCStr("resource vanished"));}),_16=new T(function(){return B(unCStr("timeout"));}),_17=new T(function(){return B(unCStr("unsupported operation"));}),_18=new T(function(){return B(unCStr("hardware fault"));}),_19=new T(function(){return B(unCStr("inappropriate type"));}),_1a=new T(function(){return B(unCStr("invalid argument"));}),_1b=new T(function(){return B(unCStr("failed"));}),_1c=new T(function(){return B(unCStr("protocol error"));}),_1d=function(_1e,_1f){switch(E(_1e)){case 0:return new F(function(){return _Q(_14,_1f);});break;case 1:return new F(function(){return _Q(_13,_1f);});break;case 2:return new F(function(){return _Q(_12,_1f);});break;case 3:return new F(function(){return _Q(_11,_1f);});break;case 4:return new F(function(){return _Q(_10,_1f);});break;case 5:return new F(function(){return _Q(_Z,_1f);});break;case 6:return new F(function(){return _Q(_Y,_1f);});break;case 7:return new F(function(){return _Q(_X,_1f);});break;case 8:return new F(function(){return _Q(_W,_1f);});break;case 9:return new F(function(){return _Q(_V,_1f);});break;case 10:return new F(function(){return _Q(_1c,_1f);});break;case 11:return new F(function(){return _Q(_1b,_1f);});break;case 12:return new F(function(){return _Q(_1a,_1f);});break;case 13:return new F(function(){return _Q(_19,_1f);});break;case 14:return new F(function(){return _Q(_18,_1f);});break;case 15:return new F(function(){return _Q(_17,_1f);});break;case 16:return new F(function(){return _Q(_16,_1f);});break;case 17:return new F(function(){return _Q(_15,_1f);});break;default:return new F(function(){return _Q(_U,_1f);});}},_1g=new T(function(){return B(unCStr("}"));}),_1h=new T(function(){return B(unCStr("{handle: "));}),_1i=function(_1j,_1k,_1l,_1m,_1n,_1o){var _1p=new T(function(){var _1q=new T(function(){var _1r=new T(function(){var _1s=E(_1m);if(!_1s._){return E(_1o);}else{var _1t=new T(function(){return B(_Q(_1s,new T(function(){return B(_Q(_O,_1o));},1)));},1);return B(_Q(_P,_1t));}},1);return B(_1d(_1k,_1r));}),_1u=E(_1l);if(!_1u._){return E(_1q);}else{return B(_Q(_1u,new T(function(){return B(_Q(_N,_1q));},1)));}}),_1v=E(_1n);if(!_1v._){var _1w=E(_1j);if(!_1w._){return E(_1p);}else{var _1x=E(_1w.a);if(!_1x._){var _1y=new T(function(){var _1z=new T(function(){return B(_Q(_1g,new T(function(){return B(_Q(_N,_1p));},1)));},1);return B(_Q(_1x.a,_1z));},1);return new F(function(){return _Q(_1h,_1y);});}else{var _1A=new T(function(){var _1B=new T(function(){return B(_Q(_1g,new T(function(){return B(_Q(_N,_1p));},1)));},1);return B(_Q(_1x.a,_1B));},1);return new F(function(){return _Q(_1h,_1A);});}}}else{return new F(function(){return _Q(_1v.a,new T(function(){return B(_Q(_N,_1p));},1));});}},_1C=function(_1D){var _1E=E(_1D);return new F(function(){return _1i(_1E.a,_1E.b,_1E.c,_1E.d,_1E.f,_w);});},_1F=function(_1G){return new T2(0,_1H,_1G);},_1I=function(_1J,_1K,_1L){var _1M=E(_1K);return new F(function(){return _1i(_1M.a,_1M.b,_1M.c,_1M.d,_1M.f,_1L);});},_1N=function(_1O,_1P){var _1Q=E(_1O);return new F(function(){return _1i(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_1P);});},_1R=44,_1S=93,_1T=91,_1U=function(_1V,_1W,_1X){var _1Y=E(_1W);if(!_1Y._){return new F(function(){return unAppCStr("[]",_1X);});}else{var _1Z=new T(function(){var _20=new T(function(){var _21=function(_22){var _23=E(_22);if(!_23._){return E(new T2(1,_1S,_1X));}else{var _24=new T(function(){return B(A2(_1V,_23.a,new T(function(){return B(_21(_23.b));})));});return new T2(1,_1R,_24);}};return B(_21(_1Y.b));});return B(A2(_1V,_1Y.a,_20));});return new T2(1,_1T,_1Z);}},_25=function(_26,_27){return new F(function(){return _1U(_1N,_26,_27);});},_28=new T3(0,_1I,_1C,_25),_1H=new T(function(){return new T5(0,_y,_28,_1F,_K,_1C);}),_29=new T(function(){return E(_1H);}),_2a=function(_2b){return E(E(_2b).c);},_2c=__Z,_2d=7,_2e=function(_2f){return new T6(0,_2c,_2d,_w,_2f,_2c,_2c);},_2g=function(_2h,_){var _2i=new T(function(){return B(A2(_2a,_29,new T(function(){return B(A1(_2e,_2h));})));});return new F(function(){return die(_2i);});},_2j=function(_2k,_){return new F(function(){return _2g(_2k,_);});},_2l=function(_2m){return new F(function(){return A1(_2j,_2m);});},_2n=function(_2o,_2p,_){var _2q=B(A1(_2o,_));return new F(function(){return A2(_2p,_2q,_);});},_2r=new T5(0,_r,_2n,_n,_l,_2l),_2s=function(_2t){return E(_2t);},_2u=new T2(0,_2r,_2s),_2v=0,_2w=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2x=function(_){return new F(function(){return __jsNull();});},_2y=function(_2z){var _2A=B(A1(_2z,_));return E(_2A);},_2B=new T(function(){return B(_2y(_2x));}),_2C=new T(function(){return E(_2B);}),_2D=function(_2E){return E(E(_2E).b);},_2F=function(_2G,_2H){var _2I=function(_){var _2J=__app1(E(_2w),E(_2H)),_2K=__eq(_2J,E(_2C));return (E(_2K)==0)?new T1(1,_2J):_2c;};return new F(function(){return A2(_2D,_2G,_2I);});},_2L=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:9:5-15"));}),_2M="canvas",_2N=new T(function(){return B(unCStr("Starting"));}),_2O=function(_2P){return new F(function(){return err(B(unAppCStr("Haste.JSON.!: unable to look up key ",new T(function(){return fromJSStr(E(_2P));}))));});},_2Q=function(_2R){return E(E(_2R).a);},_2S=function(_2T,_2U){return (!B(A3(_2Q,_2V,_2T,_2U)))?true:false;},_2W=function(_2X,_2Y){var _2Z=strEq(E(_2X),E(_2Y));return (E(_2Z)==0)?false:true;},_30=function(_31,_32){return new F(function(){return _2W(_31,_32);});},_2V=new T(function(){return new T2(0,_30,_2S);}),_33=function(_34,_35,_36){while(1){var _37=E(_36);if(!_37._){return __Z;}else{var _38=E(_37.a);if(!B(A3(_2Q,_34,_35,_38.a))){_36=_37.b;continue;}else{return new T1(1,_38.b);}}}},_39=function(_3a,_3b){var _3c=E(_3a);if(_3c._==4){var _3d=B(_33(_2V,_3b,_3c.a));if(!_3d._){return new F(function(){return _2O(_3b);});}else{return E(_3d.a);}}else{return new F(function(){return _2O(_3b);});}},_3e=new T1(1,_2v),_3f="()",_3g=function(_3h){var _3i=strEq(_3h,E(_3f));return (E(_3i)==0)?__Z:E(_3e);},_3j=function(_3k){return new F(function(){return _3g(E(_3k));});},_3l=function(_3m){return E(_3f);},_3n=new T2(0,_3l,_3j),_3o=function(_3p){return new F(function(){return jsParseJSON(E(_3p));});},_3q="]",_3r="}",_3s=":",_3t=",",_3u=new T(function(){return eval("JSON.stringify");}),_3v="false",_3w="null",_3x="[",_3y="{",_3z="\"",_3A="true",_3B=function(_3C,_3D){var _3E=E(_3D);switch(_3E._){case 0:return new T2(0,new T(function(){return jsShow(_3E.a);}),_3C);case 1:return new T2(0,new T(function(){var _3F=__app1(E(_3u),_3E.a);return String(_3F);}),_3C);case 2:return (!E(_3E.a))?new T2(0,_3v,_3C):new T2(0,_3A,_3C);case 3:var _3G=E(_3E.a);if(!_3G._){return new T2(0,_3x,new T2(1,_3q,_3C));}else{var _3H=new T(function(){var _3I=new T(function(){var _3J=function(_3K){var _3L=E(_3K);if(!_3L._){return E(new T2(1,_3q,_3C));}else{var _3M=new T(function(){var _3N=B(_3B(new T(function(){return B(_3J(_3L.b));}),_3L.a));return new T2(1,_3N.a,_3N.b);});return new T2(1,_3t,_3M);}};return B(_3J(_3G.b));}),_3O=B(_3B(_3I,_3G.a));return new T2(1,_3O.a,_3O.b);});return new T2(0,_3x,_3H);}break;case 4:var _3P=E(_3E.a);if(!_3P._){return new T2(0,_3y,new T2(1,_3r,_3C));}else{var _3Q=E(_3P.a),_3R=new T(function(){var _3S=new T(function(){var _3T=function(_3U){var _3V=E(_3U);if(!_3V._){return E(new T2(1,_3r,_3C));}else{var _3W=E(_3V.a),_3X=new T(function(){var _3Y=B(_3B(new T(function(){return B(_3T(_3V.b));}),_3W.b));return new T2(1,_3Y.a,_3Y.b);});return new T2(1,_3t,new T2(1,_3z,new T2(1,_3W.a,new T2(1,_3z,new T2(1,_3s,_3X)))));}};return B(_3T(_3P.b));}),_3Z=B(_3B(_3S,_3Q.b));return new T2(1,_3Z.a,_3Z.b);});return new T2(0,_3y,new T2(1,new T(function(){var _40=__app1(E(_3u),E(_3Q.a));return String(_40);}),new T2(1,_3s,_3R)));}break;default:return new T2(0,_3w,_3C);}},_41=new T(function(){return toJSStr(_w);}),_42=function(_43){var _44=B(_3B(_w,_43)),_45=jsCat(new T2(1,_44.a,_44.b),E(_41));return E(_45);},_46=function(_47){return new F(function(){return _42(_47);});},_48=new T2(0,_46,_3o),_49=function(_){return _2v;},_4a=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_4b=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_4c=function(_4d,_4e,_){var _4f=__app1(E(_4a),_4e),_4g=B(A2(_4d,_4e,_)),_4h=__app1(E(_4b),_4e);return new F(function(){return _49(_);});},_4i=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_4j=function(_4k,_4l,_){var _4m=__app1(E(_4a),_4l),_4n=B(A2(_4k,_4l,_)),_4o=__app1(E(_4i),_4l);return new F(function(){return _49(_);});},_4p=function(_4q,_4r){var _4s=E(_4r);if(!_4s._){return __Z;}else{var _4t=_4s.a,_4u=E(_4q);return (_4u==1)?new T2(1,_4t,_w):new T2(1,_4t,new T(function(){return B(_4p(_4u-1|0,_4s.b));}));}},_4v=function(_4w,_4x){while(1){var _4y=E(_4w);if(!_4y._){return E(_4x);}else{var _4z=new T2(1,_4y.a,_4x);_4w=_4y.b;_4x=_4z;continue;}}},_4A=new T(function(){return B(_4v(_w,_w));}),_4B=function(_4C,_4D){if(0>=_4C){return E(_4A);}else{return new F(function(){return _4v(B(_4p(_4C,B(_4v(_4D,_w)))),_w);});}},_4E=0,_4F=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_4G=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_4H=function(_4I,_4J,_){var _4K=E(_4I);if(!_4K._){return _2v;}else{var _4L=E(_4K.a),_4M=E(_4J),_4N=__app3(E(_4F),_4M,E(_4L.a),E(_4L.b)),_4O=E(_4K.b);if(!_4O._){return _2v;}else{var _4P=E(_4O.a),_4Q=E(_4G),_4R=__app3(_4Q,_4M,E(_4P.a),E(_4P.b)),_4S=function(_4T,_){while(1){var _4U=E(_4T);if(!_4U._){return _2v;}else{var _4V=E(_4U.a),_4W=__app3(_4Q,_4M,E(_4V.a),E(_4V.b));_4T=_4U.b;continue;}}};return new F(function(){return _4S(_4O.b,_);});}}},_4X=800,_4Y=50,_4Z=new T2(0,_4X,_4Y),_50=new T2(1,_4Z,_w),_51=0,_52=new T2(0,_51,_4Y),_53=new T2(1,_52,_50),_54=100,_55=new T2(0,_4X,_54),_56=new T2(1,_55,_w),_57=new T2(0,_51,_54),_58=new T2(1,_57,_56),_59=150,_5a=new T2(0,_4X,_59),_5b=new T2(1,_5a,_w),_5c=new T2(0,_51,_59),_5d=new T2(1,_5c,_5b),_5e=200,_5f=new T2(0,_4X,_5e),_5g=new T2(1,_5f,_w),_5h=new T2(0,_51,_5e),_5i=new T2(1,_5h,_5g),_5j=250,_5k=new T2(0,_4X,_5j),_5l=new T2(1,_5k,_w),_5m=new T2(0,_51,_5j),_5n=new T2(1,_5m,_5l),_5o=function(_5p,_){var _5q=B(_4H(_5n,_5p,_)),_5r=B(_4H(_5i,_5p,_)),_5s=B(_4H(_5d,_5p,_)),_5t=B(_4H(_58,_5p,_));return new F(function(){return _4H(_53,_5p,_);});},_5u="POST",_5v="GET",_5w="=",_5x="&",_5y=function(_5z,_5A){var _5B=E(_5A);return (_5B._==0)?__Z:new T2(1,new T(function(){return B(A1(_5z,_5B.a));}),new T(function(){return B(_5y(_5z,_5B.b));}));},_5C=function(_5D){return E(E(_5D).a);},_5E=function(_5F,_5G,_5H){var _5I=function(_5J){var _5K=E(_5J);return new F(function(){return jsCat(new T2(1,new T(function(){return B(A2(_5C,_5F,_5K.a));}),new T2(1,new T(function(){return B(A2(_5C,_5G,_5K.b));}),_w)),E(_5w));});},_5L=jsCat(B(_5y(_5I,_5H)),E(_5x));return E(_5L);},_5M=new T(function(){return eval("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");}),_5N=function(_5O){return E(E(_5O).b);},_5P=new T(function(){return toJSStr(_w);}),_5Q="?",_5R=function(_5S){return new F(function(){return toJSStr(E(_5S));});},_5T=function(_5U,_5V,_5W,_5X,_5Y,_5Z,_60,_61){var _62=new T(function(){return B(_5E(_5V,_5W,_60));}),_63=new T(function(){return B(_5R(_5Z));}),_64=function(_){var _65=function(_66){var _67=function(_68){var _69=function(_6a){var _6b=new T(function(){return B(_5N(_5X));}),_6c=function(_6d,_){var _6e=new T(function(){var _6f=E(_6d),_6g=__eq(_6f,E(_2C));if(!E(_6g)){return B(A1(_6b,new T(function(){return String(_6f);})));}else{return __Z;}}),_6h=B(A2(_61,_6e,_));return _2C;},_6i=__createJSFunc(2,E(_6c)),_6j=__app5(E(_5M),_66,_68,true,_6a,_6i);return _2v;};if(!E(_5Y)){return new F(function(){return _69(E(_5P));});}else{var _6k=E(_60);if(!_6k._){return new F(function(){return _69(E(_5P));});}else{return new F(function(){return _69(B(_5E(_5V,_5W,_6k)));});}}};if(!E(_5Y)){if(!E(_60)._){return new F(function(){return _67(toJSStr(E(_5Z)));});}else{var _6l=jsCat(new T2(1,_63,new T2(1,_62,_w)),E(_5Q));return new F(function(){return _67(_6l);});}}else{return new F(function(){return _67(toJSStr(E(_5Z)));});}};if(!E(_5Y)){return new F(function(){return _65(E(_5v));});}else{return new F(function(){return _65(E(_5u));});}};return new F(function(){return A2(_2D,_5U,_64);});},_6m=new T(function(){return B(unCStr(": empty list"));}),_6n=new T(function(){return B(unCStr("Prelude."));}),_6o=function(_6p){return new F(function(){return err(B(_Q(_6n,new T(function(){return B(_Q(_6p,_6m));},1))));});},_6q=new T(function(){return B(unCStr("head"));}),_6r=new T(function(){return B(_6o(_6q));}),_6s=new T(function(){return eval("(function(e){e.width = e.width;})");}),_6t=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_6u=new T(function(){return B(err(_6t));}),_6v=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_6w=new T(function(){return B(err(_6v));}),_6x=new T(function(){return B(unCStr("base"));}),_6y=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6z=new T(function(){return B(unCStr("PatternMatchFail"));}),_6A=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6x,_6y,_6z),_6B=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6A,_w,_w),_6C=function(_6D){return E(_6B);},_6E=function(_6F){var _6G=E(_6F);return new F(function(){return _C(B(_A(_6G.a)),_6C,_6G.b);});},_6H=function(_6I){return E(E(_6I).a);},_6J=function(_6K){return new T2(0,_6L,_6K);},_6M=function(_6N,_6O){return new F(function(){return _Q(E(_6N).a,_6O);});},_6P=function(_6Q,_6R){return new F(function(){return _1U(_6M,_6Q,_6R);});},_6S=function(_6T,_6U,_6V){return new F(function(){return _Q(E(_6U).a,_6V);});},_6W=new T3(0,_6S,_6H,_6P),_6L=new T(function(){return new T5(0,_6C,_6W,_6J,_6E,_6H);}),_6X=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6Y=function(_6Z,_70){return new F(function(){return die(new T(function(){return B(A2(_2a,_70,_6Z));}));});},_71=function(_72,_73){return new F(function(){return _6Y(_72,_73);});},_74=function(_75,_76){var _77=E(_76);if(!_77._){return new T2(0,_w,_w);}else{var _78=_77.a;if(!B(A1(_75,_78))){return new T2(0,_w,_77);}else{var _79=new T(function(){var _7a=B(_74(_75,_77.b));return new T2(0,_7a.a,_7a.b);});return new T2(0,new T2(1,_78,new T(function(){return E(E(_79).a);})),new T(function(){return E(E(_79).b);}));}}},_7b=32,_7c=new T(function(){return B(unCStr("\n"));}),_7d=function(_7e){return (E(_7e)==124)?false:true;},_7f=function(_7g,_7h){var _7i=B(_74(_7d,B(unCStr(_7g)))),_7j=_7i.a,_7k=function(_7l,_7m){var _7n=new T(function(){var _7o=new T(function(){return B(_Q(_7h,new T(function(){return B(_Q(_7m,_7c));},1)));});return B(unAppCStr(": ",_7o));},1);return new F(function(){return _Q(_7l,_7n);});},_7p=E(_7i.b);if(!_7p._){return new F(function(){return _7k(_7j,_w);});}else{if(E(_7p.a)==124){return new F(function(){return _7k(_7j,new T2(1,_7b,_7p.b));});}else{return new F(function(){return _7k(_7j,_w);});}}},_7q=function(_7r){return new F(function(){return _71(new T1(0,new T(function(){return B(_7f(_7r,_6X));})),_6L);});},_7s=new T(function(){return B(_7q("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7t=function(_7u,_7v){while(1){var _7w=B((function(_7x,_7y){var _7z=E(_7x);switch(_7z._){case 0:var _7A=E(_7y);if(!_7A._){return __Z;}else{_7u=B(A1(_7z.a,_7A.a));_7v=_7A.b;return __continue;}break;case 1:var _7B=B(A1(_7z.a,_7y)),_7C=_7y;_7u=_7B;_7v=_7C;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_7z.a,_7y),new T(function(){return B(_7t(_7z.b,_7y));}));default:return E(_7z.a);}})(_7u,_7v));if(_7w!=__continue){return _7w;}}},_7D=function(_7E,_7F){var _7G=function(_7H){var _7I=E(_7F);if(_7I._==3){return new T2(3,_7I.a,new T(function(){return B(_7D(_7E,_7I.b));}));}else{var _7J=E(_7E);if(_7J._==2){return E(_7I);}else{var _7K=E(_7I);if(_7K._==2){return E(_7J);}else{var _7L=function(_7M){var _7N=E(_7K);if(_7N._==4){var _7O=function(_7P){return new T1(4,new T(function(){return B(_Q(B(_7t(_7J,_7P)),_7N.a));}));};return new T1(1,_7O);}else{var _7Q=E(_7J);if(_7Q._==1){var _7R=_7Q.a,_7S=E(_7N);if(!_7S._){return new T1(1,function(_7T){return new F(function(){return _7D(B(A1(_7R,_7T)),_7S);});});}else{var _7U=function(_7V){return new F(function(){return _7D(B(A1(_7R,_7V)),new T(function(){return B(A1(_7S.a,_7V));}));});};return new T1(1,_7U);}}else{var _7W=E(_7N);if(!_7W._){return E(_7s);}else{var _7X=function(_7Y){return new F(function(){return _7D(_7Q,new T(function(){return B(A1(_7W.a,_7Y));}));});};return new T1(1,_7X);}}}},_7Z=E(_7J);switch(_7Z._){case 1:var _80=E(_7K);if(_80._==4){var _81=function(_82){return new T1(4,new T(function(){return B(_Q(B(_7t(B(A1(_7Z.a,_82)),_82)),_80.a));}));};return new T1(1,_81);}else{return new F(function(){return _7L(_);});}break;case 4:var _83=_7Z.a,_84=E(_7K);switch(_84._){case 0:var _85=function(_86){var _87=new T(function(){return B(_Q(_83,new T(function(){return B(_7t(_84,_86));},1)));});return new T1(4,_87);};return new T1(1,_85);case 1:var _88=function(_89){var _8a=new T(function(){return B(_Q(_83,new T(function(){return B(_7t(B(A1(_84.a,_89)),_89));},1)));});return new T1(4,_8a);};return new T1(1,_88);default:return new T1(4,new T(function(){return B(_Q(_83,_84.a));}));}break;default:return new F(function(){return _7L(_);});}}}}},_8b=E(_7E);switch(_8b._){case 0:var _8c=E(_7F);if(!_8c._){var _8d=function(_8e){return new F(function(){return _7D(B(A1(_8b.a,_8e)),new T(function(){return B(A1(_8c.a,_8e));}));});};return new T1(0,_8d);}else{return new F(function(){return _7G(_);});}break;case 3:return new T2(3,_8b.a,new T(function(){return B(_7D(_8b.b,_7F));}));default:return new F(function(){return _7G(_);});}},_8f=new T(function(){return B(unCStr("("));}),_8g=new T(function(){return B(unCStr(")"));}),_8h=function(_8i,_8j){while(1){var _8k=E(_8i);if(!_8k._){return (E(_8j)._==0)?true:false;}else{var _8l=E(_8j);if(!_8l._){return false;}else{if(E(_8k.a)!=E(_8l.a)){return false;}else{_8i=_8k.b;_8j=_8l.b;continue;}}}}},_8m=function(_8n,_8o){return E(_8n)!=E(_8o);},_8p=function(_8q,_8r){return E(_8q)==E(_8r);},_8s=new T2(0,_8p,_8m),_8t=function(_8u,_8v){while(1){var _8w=E(_8u);if(!_8w._){return (E(_8v)._==0)?true:false;}else{var _8x=E(_8v);if(!_8x._){return false;}else{if(E(_8w.a)!=E(_8x.a)){return false;}else{_8u=_8w.b;_8v=_8x.b;continue;}}}}},_8y=function(_8z,_8A){return (!B(_8t(_8z,_8A)))?true:false;},_8B=new T2(0,_8t,_8y),_8C=function(_8D,_8E){var _8F=E(_8D);switch(_8F._){case 0:return new T1(0,function(_8G){return new F(function(){return _8C(B(A1(_8F.a,_8G)),_8E);});});case 1:return new T1(1,function(_8H){return new F(function(){return _8C(B(A1(_8F.a,_8H)),_8E);});});case 2:return new T0(2);case 3:return new F(function(){return _7D(B(A1(_8E,_8F.a)),new T(function(){return B(_8C(_8F.b,_8E));}));});break;default:var _8I=function(_8J){var _8K=E(_8J);if(!_8K._){return __Z;}else{var _8L=E(_8K.a);return new F(function(){return _Q(B(_7t(B(A1(_8E,_8L.a)),_8L.b)),new T(function(){return B(_8I(_8K.b));},1));});}},_8M=B(_8I(_8F.a));return (_8M._==0)?new T0(2):new T1(4,_8M);}},_8N=new T0(2),_8O=function(_8P){return new T2(3,_8P,_8N);},_8Q=function(_8R,_8S){var _8T=E(_8R);if(!_8T){return new F(function(){return A1(_8S,_2v);});}else{var _8U=new T(function(){return B(_8Q(_8T-1|0,_8S));});return new T1(0,function(_8V){return E(_8U);});}},_8W=function(_8X,_8Y,_8Z){var _90=new T(function(){return B(A1(_8X,_8O));}),_91=function(_92,_93,_94,_95){while(1){var _96=B((function(_97,_98,_99,_9a){var _9b=E(_97);switch(_9b._){case 0:var _9c=E(_98);if(!_9c._){return new F(function(){return A1(_8Y,_9a);});}else{var _9d=_99+1|0,_9e=_9a;_92=B(A1(_9b.a,_9c.a));_93=_9c.b;_94=_9d;_95=_9e;return __continue;}break;case 1:var _9f=B(A1(_9b.a,_98)),_9g=_98,_9d=_99,_9e=_9a;_92=_9f;_93=_9g;_94=_9d;_95=_9e;return __continue;case 2:return new F(function(){return A1(_8Y,_9a);});break;case 3:var _9h=new T(function(){return B(_8C(_9b,_9a));});return new F(function(){return _8Q(_99,function(_9i){return E(_9h);});});break;default:return new F(function(){return _8C(_9b,_9a);});}})(_92,_93,_94,_95));if(_96!=__continue){return _96;}}};return function(_9j){return new F(function(){return _91(_90,_9j,0,_8Z);});};},_9k=function(_9l){return new F(function(){return A1(_9l,_w);});},_9m=function(_9n,_9o){var _9p=function(_9q){var _9r=E(_9q);if(!_9r._){return E(_9k);}else{var _9s=_9r.a;if(!B(A1(_9n,_9s))){return E(_9k);}else{var _9t=new T(function(){return B(_9p(_9r.b));}),_9u=function(_9v){var _9w=new T(function(){return B(A1(_9t,function(_9x){return new F(function(){return A1(_9v,new T2(1,_9s,_9x));});}));});return new T1(0,function(_9y){return E(_9w);});};return E(_9u);}}};return function(_9z){return new F(function(){return A2(_9p,_9z,_9o);});};},_9A=new T0(6),_9B=new T(function(){return B(unCStr("valDig: Bad base"));}),_9C=new T(function(){return B(err(_9B));}),_9D=function(_9E,_9F){var _9G=function(_9H,_9I){var _9J=E(_9H);if(!_9J._){var _9K=new T(function(){return B(A1(_9I,_w));});return function(_9L){return new F(function(){return A1(_9L,_9K);});};}else{var _9M=E(_9J.a),_9N=function(_9O){var _9P=new T(function(){return B(_9G(_9J.b,function(_9Q){return new F(function(){return A1(_9I,new T2(1,_9O,_9Q));});}));}),_9R=function(_9S){var _9T=new T(function(){return B(A1(_9P,_9S));});return new T1(0,function(_9U){return E(_9T);});};return E(_9R);};switch(E(_9E)){case 8:if(48>_9M){var _9V=new T(function(){return B(A1(_9I,_w));});return function(_9W){return new F(function(){return A1(_9W,_9V);});};}else{if(_9M>55){var _9X=new T(function(){return B(A1(_9I,_w));});return function(_9Y){return new F(function(){return A1(_9Y,_9X);});};}else{return new F(function(){return _9N(_9M-48|0);});}}break;case 10:if(48>_9M){var _9Z=new T(function(){return B(A1(_9I,_w));});return function(_a0){return new F(function(){return A1(_a0,_9Z);});};}else{if(_9M>57){var _a1=new T(function(){return B(A1(_9I,_w));});return function(_a2){return new F(function(){return A1(_a2,_a1);});};}else{return new F(function(){return _9N(_9M-48|0);});}}break;case 16:if(48>_9M){if(97>_9M){if(65>_9M){var _a3=new T(function(){return B(A1(_9I,_w));});return function(_a4){return new F(function(){return A1(_a4,_a3);});};}else{if(_9M>70){var _a5=new T(function(){return B(A1(_9I,_w));});return function(_a6){return new F(function(){return A1(_a6,_a5);});};}else{return new F(function(){return _9N((_9M-65|0)+10|0);});}}}else{if(_9M>102){if(65>_9M){var _a7=new T(function(){return B(A1(_9I,_w));});return function(_a8){return new F(function(){return A1(_a8,_a7);});};}else{if(_9M>70){var _a9=new T(function(){return B(A1(_9I,_w));});return function(_aa){return new F(function(){return A1(_aa,_a9);});};}else{return new F(function(){return _9N((_9M-65|0)+10|0);});}}}else{return new F(function(){return _9N((_9M-97|0)+10|0);});}}}else{if(_9M>57){if(97>_9M){if(65>_9M){var _ab=new T(function(){return B(A1(_9I,_w));});return function(_ac){return new F(function(){return A1(_ac,_ab);});};}else{if(_9M>70){var _ad=new T(function(){return B(A1(_9I,_w));});return function(_ae){return new F(function(){return A1(_ae,_ad);});};}else{return new F(function(){return _9N((_9M-65|0)+10|0);});}}}else{if(_9M>102){if(65>_9M){var _af=new T(function(){return B(A1(_9I,_w));});return function(_ag){return new F(function(){return A1(_ag,_af);});};}else{if(_9M>70){var _ah=new T(function(){return B(A1(_9I,_w));});return function(_ai){return new F(function(){return A1(_ai,_ah);});};}else{return new F(function(){return _9N((_9M-65|0)+10|0);});}}}else{return new F(function(){return _9N((_9M-97|0)+10|0);});}}}else{return new F(function(){return _9N(_9M-48|0);});}}break;default:return E(_9C);}}},_aj=function(_ak){var _al=E(_ak);if(!_al._){return new T0(2);}else{return new F(function(){return A1(_9F,_al);});}};return function(_am){return new F(function(){return A3(_9G,_am,_2s,_aj);});};},_an=16,_ao=8,_ap=function(_aq){var _ar=function(_as){return new F(function(){return A1(_aq,new T1(5,new T2(0,_ao,_as)));});},_at=function(_au){return new F(function(){return A1(_aq,new T1(5,new T2(0,_an,_au)));});},_av=function(_aw){switch(E(_aw)){case 79:return new T1(1,B(_9D(_ao,_ar)));case 88:return new T1(1,B(_9D(_an,_at)));case 111:return new T1(1,B(_9D(_ao,_ar)));case 120:return new T1(1,B(_9D(_an,_at)));default:return new T0(2);}};return function(_ax){return (E(_ax)==48)?E(new T1(0,_av)):new T0(2);};},_ay=function(_az){return new T1(0,B(_ap(_az)));},_aA=function(_aB){return new F(function(){return A1(_aB,_2c);});},_aC=function(_aD){return new F(function(){return A1(_aD,_2c);});},_aE=10,_aF=new T1(0,1),_aG=new T1(0,2147483647),_aH=function(_aI,_aJ){while(1){var _aK=E(_aI);if(!_aK._){var _aL=_aK.a,_aM=E(_aJ);if(!_aM._){var _aN=_aM.a,_aO=addC(_aL,_aN);if(!E(_aO.b)){return new T1(0,_aO.a);}else{_aI=new T1(1,I_fromInt(_aL));_aJ=new T1(1,I_fromInt(_aN));continue;}}else{_aI=new T1(1,I_fromInt(_aL));_aJ=_aM;continue;}}else{var _aP=E(_aJ);if(!_aP._){_aI=_aK;_aJ=new T1(1,I_fromInt(_aP.a));continue;}else{return new T1(1,I_add(_aK.a,_aP.a));}}}},_aQ=new T(function(){return B(_aH(_aG,_aF));}),_aR=function(_aS){var _aT=E(_aS);if(!_aT._){var _aU=E(_aT.a);return (_aU==(-2147483648))?E(_aQ):new T1(0, -_aU);}else{return new T1(1,I_negate(_aT.a));}},_aV=new T1(0,10),_aW=function(_aX,_aY){while(1){var _aZ=E(_aX);if(!_aZ._){return E(_aY);}else{var _b0=_aY+1|0;_aX=_aZ.b;_aY=_b0;continue;}}},_b1=function(_b2){return new T1(0,_b2);},_b3=function(_b4){return new F(function(){return _b1(E(_b4));});},_b5=new T(function(){return B(unCStr("this should not happen"));}),_b6=new T(function(){return B(err(_b5));}),_b7=function(_b8,_b9){while(1){var _ba=E(_b8);if(!_ba._){var _bb=_ba.a,_bc=E(_b9);if(!_bc._){var _bd=_bc.a;if(!(imul(_bb,_bd)|0)){return new T1(0,imul(_bb,_bd)|0);}else{_b8=new T1(1,I_fromInt(_bb));_b9=new T1(1,I_fromInt(_bd));continue;}}else{_b8=new T1(1,I_fromInt(_bb));_b9=_bc;continue;}}else{var _be=E(_b9);if(!_be._){_b8=_ba;_b9=new T1(1,I_fromInt(_be.a));continue;}else{return new T1(1,I_mul(_ba.a,_be.a));}}}},_bf=function(_bg,_bh){var _bi=E(_bh);if(!_bi._){return __Z;}else{var _bj=E(_bi.b);return (_bj._==0)?E(_b6):new T2(1,B(_aH(B(_b7(_bi.a,_bg)),_bj.a)),new T(function(){return B(_bf(_bg,_bj.b));}));}},_bk=new T1(0,0),_bl=function(_bm,_bn,_bo){while(1){var _bp=B((function(_bq,_br,_bs){var _bt=E(_bs);if(!_bt._){return E(_bk);}else{if(!E(_bt.b)._){return E(_bt.a);}else{var _bu=E(_br);if(_bu<=40){var _bv=function(_bw,_bx){while(1){var _by=E(_bx);if(!_by._){return E(_bw);}else{var _bz=B(_aH(B(_b7(_bw,_bq)),_by.a));_bw=_bz;_bx=_by.b;continue;}}};return new F(function(){return _bv(_bk,_bt);});}else{var _bA=B(_b7(_bq,_bq));if(!(_bu%2)){var _bB=B(_bf(_bq,_bt));_bm=_bA;_bn=quot(_bu+1|0,2);_bo=_bB;return __continue;}else{var _bB=B(_bf(_bq,new T2(1,_bk,_bt)));_bm=_bA;_bn=quot(_bu+1|0,2);_bo=_bB;return __continue;}}}}})(_bm,_bn,_bo));if(_bp!=__continue){return _bp;}}},_bC=function(_bD,_bE){return new F(function(){return _bl(_bD,new T(function(){return B(_aW(_bE,0));},1),B(_5y(_b3,_bE)));});},_bF=function(_bG){var _bH=new T(function(){var _bI=new T(function(){var _bJ=function(_bK){return new F(function(){return A1(_bG,new T1(1,new T(function(){return B(_bC(_aV,_bK));})));});};return new T1(1,B(_9D(_aE,_bJ)));}),_bL=function(_bM){if(E(_bM)==43){var _bN=function(_bO){return new F(function(){return A1(_bG,new T1(1,new T(function(){return B(_bC(_aV,_bO));})));});};return new T1(1,B(_9D(_aE,_bN)));}else{return new T0(2);}},_bP=function(_bQ){if(E(_bQ)==45){var _bR=function(_bS){return new F(function(){return A1(_bG,new T1(1,new T(function(){return B(_aR(B(_bC(_aV,_bS))));})));});};return new T1(1,B(_9D(_aE,_bR)));}else{return new T0(2);}};return B(_7D(B(_7D(new T1(0,_bP),new T1(0,_bL))),_bI));});return new F(function(){return _7D(new T1(0,function(_bT){return (E(_bT)==101)?E(_bH):new T0(2);}),new T1(0,function(_bU){return (E(_bU)==69)?E(_bH):new T0(2);}));});},_bV=function(_bW){var _bX=function(_bY){return new F(function(){return A1(_bW,new T1(1,_bY));});};return function(_bZ){return (E(_bZ)==46)?new T1(1,B(_9D(_aE,_bX))):new T0(2);};},_c0=function(_c1){return new T1(0,B(_bV(_c1)));},_c2=function(_c3){var _c4=function(_c5){var _c6=function(_c7){return new T1(1,B(_8W(_bF,_aA,function(_c8){return new F(function(){return A1(_c3,new T1(5,new T3(1,_c5,_c7,_c8)));});})));};return new T1(1,B(_8W(_c0,_aC,_c6)));};return new F(function(){return _9D(_aE,_c4);});},_c9=function(_ca){return new T1(1,B(_c2(_ca)));},_cb=function(_cc,_cd,_ce){while(1){var _cf=E(_ce);if(!_cf._){return false;}else{if(!B(A3(_2Q,_cc,_cd,_cf.a))){_ce=_cf.b;continue;}else{return true;}}}},_cg=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_ch=function(_ci){return new F(function(){return _cb(_8s,_ci,_cg);});},_cj=false,_ck=true,_cl=function(_cm){var _cn=new T(function(){return B(A1(_cm,_ao));}),_co=new T(function(){return B(A1(_cm,_an));});return function(_cp){switch(E(_cp)){case 79:return E(_cn);case 88:return E(_co);case 111:return E(_cn);case 120:return E(_co);default:return new T0(2);}};},_cq=function(_cr){return new T1(0,B(_cl(_cr)));},_cs=function(_ct){return new F(function(){return A1(_ct,_aE);});},_cu=function(_cv,_cw){var _cx=jsShowI(_cv);return new F(function(){return _Q(fromJSStr(_cx),_cw);});},_cy=41,_cz=40,_cA=function(_cB,_cC,_cD){if(_cC>=0){return new F(function(){return _cu(_cC,_cD);});}else{if(_cB<=6){return new F(function(){return _cu(_cC,_cD);});}else{return new T2(1,_cz,new T(function(){var _cE=jsShowI(_cC);return B(_Q(fromJSStr(_cE),new T2(1,_cy,_cD)));}));}}},_cF=function(_cG){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_cA(9,_cG,_w));}))));});},_cH=function(_cI){var _cJ=E(_cI);if(!_cJ._){return E(_cJ.a);}else{return new F(function(){return I_toInt(_cJ.a);});}},_cK=function(_cL,_cM){var _cN=E(_cL);if(!_cN._){var _cO=_cN.a,_cP=E(_cM);return (_cP._==0)?_cO<=_cP.a:I_compareInt(_cP.a,_cO)>=0;}else{var _cQ=_cN.a,_cR=E(_cM);return (_cR._==0)?I_compareInt(_cQ,_cR.a)<=0:I_compare(_cQ,_cR.a)<=0;}},_cS=function(_cT){return new T0(2);},_cU=function(_cV){var _cW=E(_cV);if(!_cW._){return E(_cS);}else{var _cX=_cW.a,_cY=E(_cW.b);if(!_cY._){return E(_cX);}else{var _cZ=new T(function(){return B(_cU(_cY));}),_d0=function(_d1){return new F(function(){return _7D(B(A1(_cX,_d1)),new T(function(){return B(A1(_cZ,_d1));}));});};return E(_d0);}}},_d2=function(_d3,_d4){var _d5=function(_d6,_d7,_d8){var _d9=E(_d6);if(!_d9._){return new F(function(){return A1(_d8,_d3);});}else{var _da=E(_d7);if(!_da._){return new T0(2);}else{if(E(_d9.a)!=E(_da.a)){return new T0(2);}else{var _db=new T(function(){return B(_d5(_d9.b,_da.b,_d8));});return new T1(0,function(_dc){return E(_db);});}}}};return function(_dd){return new F(function(){return _d5(_d3,_dd,_d4);});};},_de=new T(function(){return B(unCStr("SO"));}),_df=14,_dg=function(_dh){var _di=new T(function(){return B(A1(_dh,_df));});return new T1(1,B(_d2(_de,function(_dj){return E(_di);})));},_dk=new T(function(){return B(unCStr("SOH"));}),_dl=1,_dm=function(_dn){var _do=new T(function(){return B(A1(_dn,_dl));});return new T1(1,B(_d2(_dk,function(_dp){return E(_do);})));},_dq=function(_dr){return new T1(1,B(_8W(_dm,_dg,_dr)));},_ds=new T(function(){return B(unCStr("NUL"));}),_dt=0,_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,_dt));});return new T1(1,B(_d2(_ds,function(_dx){return E(_dw);})));},_dy=new T(function(){return B(unCStr("STX"));}),_dz=2,_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,_dz));});return new T1(1,B(_d2(_dy,function(_dD){return E(_dC);})));},_dE=new T(function(){return B(unCStr("ETX"));}),_dF=3,_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,_dF));});return new T1(1,B(_d2(_dE,function(_dJ){return E(_dI);})));},_dK=new T(function(){return B(unCStr("EOT"));}),_dL=4,_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,_dL));});return new T1(1,B(_d2(_dK,function(_dP){return E(_dO);})));},_dQ=new T(function(){return B(unCStr("ENQ"));}),_dR=5,_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,_dR));});return new T1(1,B(_d2(_dQ,function(_dV){return E(_dU);})));},_dW=new T(function(){return B(unCStr("ACK"));}),_dX=6,_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,_dX));});return new T1(1,B(_d2(_dW,function(_e1){return E(_e0);})));},_e2=new T(function(){return B(unCStr("BEL"));}),_e3=7,_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,_e3));});return new T1(1,B(_d2(_e2,function(_e7){return E(_e6);})));},_e8=new T(function(){return B(unCStr("BS"));}),_e9=8,_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,_e9));});return new T1(1,B(_d2(_e8,function(_ed){return E(_ec);})));},_ee=new T(function(){return B(unCStr("HT"));}),_ef=9,_eg=function(_eh){var _ei=new T(function(){return B(A1(_eh,_ef));});return new T1(1,B(_d2(_ee,function(_ej){return E(_ei);})));},_ek=new T(function(){return B(unCStr("LF"));}),_el=10,_em=function(_en){var _eo=new T(function(){return B(A1(_en,_el));});return new T1(1,B(_d2(_ek,function(_ep){return E(_eo);})));},_eq=new T(function(){return B(unCStr("VT"));}),_er=11,_es=function(_et){var _eu=new T(function(){return B(A1(_et,_er));});return new T1(1,B(_d2(_eq,function(_ev){return E(_eu);})));},_ew=new T(function(){return B(unCStr("FF"));}),_ex=12,_ey=function(_ez){var _eA=new T(function(){return B(A1(_ez,_ex));});return new T1(1,B(_d2(_ew,function(_eB){return E(_eA);})));},_eC=new T(function(){return B(unCStr("CR"));}),_eD=13,_eE=function(_eF){var _eG=new T(function(){return B(A1(_eF,_eD));});return new T1(1,B(_d2(_eC,function(_eH){return E(_eG);})));},_eI=new T(function(){return B(unCStr("SI"));}),_eJ=15,_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,_eJ));});return new T1(1,B(_d2(_eI,function(_eN){return E(_eM);})));},_eO=new T(function(){return B(unCStr("DLE"));}),_eP=16,_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,_eP));});return new T1(1,B(_d2(_eO,function(_eT){return E(_eS);})));},_eU=new T(function(){return B(unCStr("DC1"));}),_eV=17,_eW=function(_eX){var _eY=new T(function(){return B(A1(_eX,_eV));});return new T1(1,B(_d2(_eU,function(_eZ){return E(_eY);})));},_f0=new T(function(){return B(unCStr("DC2"));}),_f1=18,_f2=function(_f3){var _f4=new T(function(){return B(A1(_f3,_f1));});return new T1(1,B(_d2(_f0,function(_f5){return E(_f4);})));},_f6=new T(function(){return B(unCStr("DC3"));}),_f7=19,_f8=function(_f9){var _fa=new T(function(){return B(A1(_f9,_f7));});return new T1(1,B(_d2(_f6,function(_fb){return E(_fa);})));},_fc=new T(function(){return B(unCStr("DC4"));}),_fd=20,_fe=function(_ff){var _fg=new T(function(){return B(A1(_ff,_fd));});return new T1(1,B(_d2(_fc,function(_fh){return E(_fg);})));},_fi=new T(function(){return B(unCStr("NAK"));}),_fj=21,_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,_fj));});return new T1(1,B(_d2(_fi,function(_fn){return E(_fm);})));},_fo=new T(function(){return B(unCStr("SYN"));}),_fp=22,_fq=function(_fr){var _fs=new T(function(){return B(A1(_fr,_fp));});return new T1(1,B(_d2(_fo,function(_ft){return E(_fs);})));},_fu=new T(function(){return B(unCStr("ETB"));}),_fv=23,_fw=function(_fx){var _fy=new T(function(){return B(A1(_fx,_fv));});return new T1(1,B(_d2(_fu,function(_fz){return E(_fy);})));},_fA=new T(function(){return B(unCStr("CAN"));}),_fB=24,_fC=function(_fD){var _fE=new T(function(){return B(A1(_fD,_fB));});return new T1(1,B(_d2(_fA,function(_fF){return E(_fE);})));},_fG=new T(function(){return B(unCStr("EM"));}),_fH=25,_fI=function(_fJ){var _fK=new T(function(){return B(A1(_fJ,_fH));});return new T1(1,B(_d2(_fG,function(_fL){return E(_fK);})));},_fM=new T(function(){return B(unCStr("SUB"));}),_fN=26,_fO=function(_fP){var _fQ=new T(function(){return B(A1(_fP,_fN));});return new T1(1,B(_d2(_fM,function(_fR){return E(_fQ);})));},_fS=new T(function(){return B(unCStr("ESC"));}),_fT=27,_fU=function(_fV){var _fW=new T(function(){return B(A1(_fV,_fT));});return new T1(1,B(_d2(_fS,function(_fX){return E(_fW);})));},_fY=new T(function(){return B(unCStr("FS"));}),_fZ=28,_g0=function(_g1){var _g2=new T(function(){return B(A1(_g1,_fZ));});return new T1(1,B(_d2(_fY,function(_g3){return E(_g2);})));},_g4=new T(function(){return B(unCStr("GS"));}),_g5=29,_g6=function(_g7){var _g8=new T(function(){return B(A1(_g7,_g5));});return new T1(1,B(_d2(_g4,function(_g9){return E(_g8);})));},_ga=new T(function(){return B(unCStr("RS"));}),_gb=30,_gc=function(_gd){var _ge=new T(function(){return B(A1(_gd,_gb));});return new T1(1,B(_d2(_ga,function(_gf){return E(_ge);})));},_gg=new T(function(){return B(unCStr("US"));}),_gh=31,_gi=function(_gj){var _gk=new T(function(){return B(A1(_gj,_gh));});return new T1(1,B(_d2(_gg,function(_gl){return E(_gk);})));},_gm=new T(function(){return B(unCStr("SP"));}),_gn=32,_go=function(_gp){var _gq=new T(function(){return B(A1(_gp,_gn));});return new T1(1,B(_d2(_gm,function(_gr){return E(_gq);})));},_gs=new T(function(){return B(unCStr("DEL"));}),_gt=127,_gu=function(_gv){var _gw=new T(function(){return B(A1(_gv,_gt));});return new T1(1,B(_d2(_gs,function(_gx){return E(_gw);})));},_gy=new T2(1,_gu,_w),_gz=new T2(1,_go,_gy),_gA=new T2(1,_gi,_gz),_gB=new T2(1,_gc,_gA),_gC=new T2(1,_g6,_gB),_gD=new T2(1,_g0,_gC),_gE=new T2(1,_fU,_gD),_gF=new T2(1,_fO,_gE),_gG=new T2(1,_fI,_gF),_gH=new T2(1,_fC,_gG),_gI=new T2(1,_fw,_gH),_gJ=new T2(1,_fq,_gI),_gK=new T2(1,_fk,_gJ),_gL=new T2(1,_fe,_gK),_gM=new T2(1,_f8,_gL),_gN=new T2(1,_f2,_gM),_gO=new T2(1,_eW,_gN),_gP=new T2(1,_eQ,_gO),_gQ=new T2(1,_eK,_gP),_gR=new T2(1,_eE,_gQ),_gS=new T2(1,_ey,_gR),_gT=new T2(1,_es,_gS),_gU=new T2(1,_em,_gT),_gV=new T2(1,_eg,_gU),_gW=new T2(1,_ea,_gV),_gX=new T2(1,_e4,_gW),_gY=new T2(1,_dY,_gX),_gZ=new T2(1,_dS,_gY),_h0=new T2(1,_dM,_gZ),_h1=new T2(1,_dG,_h0),_h2=new T2(1,_dA,_h1),_h3=new T2(1,_du,_h2),_h4=new T2(1,_dq,_h3),_h5=new T(function(){return B(_cU(_h4));}),_h6=34,_h7=new T1(0,1114111),_h8=92,_h9=39,_ha=function(_hb){var _hc=new T(function(){return B(A1(_hb,_e3));}),_hd=new T(function(){return B(A1(_hb,_e9));}),_he=new T(function(){return B(A1(_hb,_ef));}),_hf=new T(function(){return B(A1(_hb,_el));}),_hg=new T(function(){return B(A1(_hb,_er));}),_hh=new T(function(){return B(A1(_hb,_ex));}),_hi=new T(function(){return B(A1(_hb,_eD));}),_hj=new T(function(){return B(A1(_hb,_h8));}),_hk=new T(function(){return B(A1(_hb,_h9));}),_hl=new T(function(){return B(A1(_hb,_h6));}),_hm=new T(function(){var _hn=function(_ho){var _hp=new T(function(){return B(_b1(E(_ho)));}),_hq=function(_hr){var _hs=B(_bC(_hp,_hr));if(!B(_cK(_hs,_h7))){return new T0(2);}else{return new F(function(){return A1(_hb,new T(function(){var _ht=B(_cH(_hs));if(_ht>>>0>1114111){return B(_cF(_ht));}else{return _ht;}}));});}};return new T1(1,B(_9D(_ho,_hq)));},_hu=new T(function(){var _hv=new T(function(){return B(A1(_hb,_gh));}),_hw=new T(function(){return B(A1(_hb,_gb));}),_hx=new T(function(){return B(A1(_hb,_g5));}),_hy=new T(function(){return B(A1(_hb,_fZ));}),_hz=new T(function(){return B(A1(_hb,_fT));}),_hA=new T(function(){return B(A1(_hb,_fN));}),_hB=new T(function(){return B(A1(_hb,_fH));}),_hC=new T(function(){return B(A1(_hb,_fB));}),_hD=new T(function(){return B(A1(_hb,_fv));}),_hE=new T(function(){return B(A1(_hb,_fp));}),_hF=new T(function(){return B(A1(_hb,_fj));}),_hG=new T(function(){return B(A1(_hb,_fd));}),_hH=new T(function(){return B(A1(_hb,_f7));}),_hI=new T(function(){return B(A1(_hb,_f1));}),_hJ=new T(function(){return B(A1(_hb,_eV));}),_hK=new T(function(){return B(A1(_hb,_eP));}),_hL=new T(function(){return B(A1(_hb,_eJ));}),_hM=new T(function(){return B(A1(_hb,_df));}),_hN=new T(function(){return B(A1(_hb,_dX));}),_hO=new T(function(){return B(A1(_hb,_dR));}),_hP=new T(function(){return B(A1(_hb,_dL));}),_hQ=new T(function(){return B(A1(_hb,_dF));}),_hR=new T(function(){return B(A1(_hb,_dz));}),_hS=new T(function(){return B(A1(_hb,_dl));}),_hT=new T(function(){return B(A1(_hb,_dt));}),_hU=function(_hV){switch(E(_hV)){case 64:return E(_hT);case 65:return E(_hS);case 66:return E(_hR);case 67:return E(_hQ);case 68:return E(_hP);case 69:return E(_hO);case 70:return E(_hN);case 71:return E(_hc);case 72:return E(_hd);case 73:return E(_he);case 74:return E(_hf);case 75:return E(_hg);case 76:return E(_hh);case 77:return E(_hi);case 78:return E(_hM);case 79:return E(_hL);case 80:return E(_hK);case 81:return E(_hJ);case 82:return E(_hI);case 83:return E(_hH);case 84:return E(_hG);case 85:return E(_hF);case 86:return E(_hE);case 87:return E(_hD);case 88:return E(_hC);case 89:return E(_hB);case 90:return E(_hA);case 91:return E(_hz);case 92:return E(_hy);case 93:return E(_hx);case 94:return E(_hw);case 95:return E(_hv);default:return new T0(2);}};return B(_7D(new T1(0,function(_hW){return (E(_hW)==94)?E(new T1(0,_hU)):new T0(2);}),new T(function(){return B(A1(_h5,_hb));})));});return B(_7D(new T1(1,B(_8W(_cq,_cs,_hn))),_hu));});return new F(function(){return _7D(new T1(0,function(_hX){switch(E(_hX)){case 34:return E(_hl);case 39:return E(_hk);case 92:return E(_hj);case 97:return E(_hc);case 98:return E(_hd);case 102:return E(_hh);case 110:return E(_hf);case 114:return E(_hi);case 116:return E(_he);case 118:return E(_hg);default:return new T0(2);}}),_hm);});},_hY=function(_hZ){return new F(function(){return A1(_hZ,_2v);});},_i0=function(_i1){var _i2=E(_i1);if(!_i2._){return E(_hY);}else{var _i3=E(_i2.a),_i4=_i3>>>0,_i5=new T(function(){return B(_i0(_i2.b));});if(_i4>887){var _i6=u_iswspace(_i3);if(!E(_i6)){return E(_hY);}else{var _i7=function(_i8){var _i9=new T(function(){return B(A1(_i5,_i8));});return new T1(0,function(_ia){return E(_i9);});};return E(_i7);}}else{var _ib=E(_i4);if(_ib==32){var _ic=function(_id){var _ie=new T(function(){return B(A1(_i5,_id));});return new T1(0,function(_if){return E(_ie);});};return E(_ic);}else{if(_ib-9>>>0>4){if(E(_ib)==160){var _ig=function(_ih){var _ii=new T(function(){return B(A1(_i5,_ih));});return new T1(0,function(_ij){return E(_ii);});};return E(_ig);}else{return E(_hY);}}else{var _ik=function(_il){var _im=new T(function(){return B(A1(_i5,_il));});return new T1(0,function(_in){return E(_im);});};return E(_ik);}}}}},_io=function(_ip){var _iq=new T(function(){return B(_io(_ip));}),_ir=function(_is){return (E(_is)==92)?E(_iq):new T0(2);},_it=function(_iu){return E(new T1(0,_ir));},_iv=new T1(1,function(_iw){return new F(function(){return A2(_i0,_iw,_it);});}),_ix=new T(function(){return B(_ha(function(_iy){return new F(function(){return A1(_ip,new T2(0,_iy,_ck));});}));}),_iz=function(_iA){var _iB=E(_iA);if(_iB==38){return E(_iq);}else{var _iC=_iB>>>0;if(_iC>887){var _iD=u_iswspace(_iB);return (E(_iD)==0)?new T0(2):E(_iv);}else{var _iE=E(_iC);return (_iE==32)?E(_iv):(_iE-9>>>0>4)?(E(_iE)==160)?E(_iv):new T0(2):E(_iv);}}};return new F(function(){return _7D(new T1(0,function(_iF){return (E(_iF)==92)?E(new T1(0,_iz)):new T0(2);}),new T1(0,function(_iG){var _iH=E(_iG);if(E(_iH)==92){return E(_ix);}else{return new F(function(){return A1(_ip,new T2(0,_iH,_cj));});}}));});},_iI=function(_iJ,_iK){var _iL=new T(function(){return B(A1(_iK,new T1(1,new T(function(){return B(A1(_iJ,_w));}))));}),_iM=function(_iN){var _iO=E(_iN),_iP=E(_iO.a);if(E(_iP)==34){if(!E(_iO.b)){return E(_iL);}else{return new F(function(){return _iI(function(_iQ){return new F(function(){return A1(_iJ,new T2(1,_iP,_iQ));});},_iK);});}}else{return new F(function(){return _iI(function(_iR){return new F(function(){return A1(_iJ,new T2(1,_iP,_iR));});},_iK);});}};return new F(function(){return _io(_iM);});},_iS=new T(function(){return B(unCStr("_\'"));}),_iT=function(_iU){var _iV=u_iswalnum(_iU);if(!E(_iV)){return new F(function(){return _cb(_8s,_iU,_iS);});}else{return true;}},_iW=function(_iX){return new F(function(){return _iT(E(_iX));});},_iY=new T(function(){return B(unCStr(",;()[]{}`"));}),_iZ=new T(function(){return B(unCStr("=>"));}),_j0=new T2(1,_iZ,_w),_j1=new T(function(){return B(unCStr("~"));}),_j2=new T2(1,_j1,_j0),_j3=new T(function(){return B(unCStr("@"));}),_j4=new T2(1,_j3,_j2),_j5=new T(function(){return B(unCStr("->"));}),_j6=new T2(1,_j5,_j4),_j7=new T(function(){return B(unCStr("<-"));}),_j8=new T2(1,_j7,_j6),_j9=new T(function(){return B(unCStr("|"));}),_ja=new T2(1,_j9,_j8),_jb=new T(function(){return B(unCStr("\\"));}),_jc=new T2(1,_jb,_ja),_jd=new T(function(){return B(unCStr("="));}),_je=new T2(1,_jd,_jc),_jf=new T(function(){return B(unCStr("::"));}),_jg=new T2(1,_jf,_je),_jh=new T(function(){return B(unCStr(".."));}),_ji=new T2(1,_jh,_jg),_jj=function(_jk){var _jl=new T(function(){return B(A1(_jk,_9A));}),_jm=new T(function(){var _jn=new T(function(){var _jo=function(_jp){var _jq=new T(function(){return B(A1(_jk,new T1(0,_jp)));});return new T1(0,function(_jr){return (E(_jr)==39)?E(_jq):new T0(2);});};return B(_ha(_jo));}),_js=function(_jt){var _ju=E(_jt);switch(E(_ju)){case 39:return new T0(2);case 92:return E(_jn);default:var _jv=new T(function(){return B(A1(_jk,new T1(0,_ju)));});return new T1(0,function(_jw){return (E(_jw)==39)?E(_jv):new T0(2);});}},_jx=new T(function(){var _jy=new T(function(){return B(_iI(_2s,_jk));}),_jz=new T(function(){var _jA=new T(function(){var _jB=new T(function(){var _jC=function(_jD){var _jE=E(_jD),_jF=u_iswalpha(_jE);return (E(_jF)==0)?(E(_jE)==95)?new T1(1,B(_9m(_iW,function(_jG){return new F(function(){return A1(_jk,new T1(3,new T2(1,_jE,_jG)));});}))):new T0(2):new T1(1,B(_9m(_iW,function(_jH){return new F(function(){return A1(_jk,new T1(3,new T2(1,_jE,_jH)));});})));};return B(_7D(new T1(0,_jC),new T(function(){return new T1(1,B(_8W(_ay,_c9,_jk)));})));}),_jI=function(_jJ){return (!B(_cb(_8s,_jJ,_cg)))?new T0(2):new T1(1,B(_9m(_ch,function(_jK){var _jL=new T2(1,_jJ,_jK);if(!B(_cb(_8B,_jL,_ji))){return new F(function(){return A1(_jk,new T1(4,_jL));});}else{return new F(function(){return A1(_jk,new T1(2,_jL));});}})));};return B(_7D(new T1(0,_jI),_jB));});return B(_7D(new T1(0,function(_jM){if(!B(_cb(_8s,_jM,_iY))){return new T0(2);}else{return new F(function(){return A1(_jk,new T1(2,new T2(1,_jM,_w)));});}}),_jA));});return B(_7D(new T1(0,function(_jN){return (E(_jN)==34)?E(_jy):new T0(2);}),_jz));});return B(_7D(new T1(0,function(_jO){return (E(_jO)==39)?E(new T1(0,_js)):new T0(2);}),_jx));});return new F(function(){return _7D(new T1(1,function(_jP){return (E(_jP)._==0)?E(_jl):new T0(2);}),_jm);});},_jQ=0,_jR=function(_jS,_jT){var _jU=new T(function(){var _jV=new T(function(){var _jW=function(_jX){var _jY=new T(function(){var _jZ=new T(function(){return B(A1(_jT,_jX));});return B(_jj(function(_k0){var _k1=E(_k0);return (_k1._==2)?(!B(_8h(_k1.a,_8g)))?new T0(2):E(_jZ):new T0(2);}));}),_k2=function(_k3){return E(_jY);};return new T1(1,function(_k4){return new F(function(){return A2(_i0,_k4,_k2);});});};return B(A2(_jS,_jQ,_jW));});return B(_jj(function(_k5){var _k6=E(_k5);return (_k6._==2)?(!B(_8h(_k6.a,_8f)))?new T0(2):E(_jV):new T0(2);}));}),_k7=function(_k8){return E(_jU);};return function(_k9){return new F(function(){return A2(_i0,_k9,_k7);});};},_ka=function(_kb,_kc){var _kd=function(_ke){var _kf=new T(function(){return B(A1(_kb,_ke));}),_kg=function(_kh){return new F(function(){return _7D(B(A1(_kf,_kh)),new T(function(){return new T1(1,B(_jR(_kd,_kh)));}));});};return E(_kg);},_ki=new T(function(){return B(A1(_kb,_kc));}),_kj=function(_kk){return new F(function(){return _7D(B(A1(_ki,_kk)),new T(function(){return new T1(1,B(_jR(_kd,_kk)));}));});};return E(_kj);},_kl=function(_km,_kn){var _ko=function(_kp,_kq){var _kr=function(_ks){return new F(function(){return A1(_kq,new T(function(){return  -E(_ks);}));});},_kt=new T(function(){return B(_jj(function(_ku){return new F(function(){return A3(_km,_ku,_kp,_kr);});}));}),_kv=function(_kw){return E(_kt);},_kx=function(_ky){return new F(function(){return A2(_i0,_ky,_kv);});},_kz=new T(function(){return B(_jj(function(_kA){var _kB=E(_kA);if(_kB._==4){var _kC=E(_kB.a);if(!_kC._){return new F(function(){return A3(_km,_kB,_kp,_kq);});}else{if(E(_kC.a)==45){if(!E(_kC.b)._){return E(new T1(1,_kx));}else{return new F(function(){return A3(_km,_kB,_kp,_kq);});}}else{return new F(function(){return A3(_km,_kB,_kp,_kq);});}}}else{return new F(function(){return A3(_km,_kB,_kp,_kq);});}}));}),_kD=function(_kE){return E(_kz);};return new T1(1,function(_kF){return new F(function(){return A2(_i0,_kF,_kD);});});};return new F(function(){return _ka(_ko,_kn);});},_kG=new T(function(){return 1/0;}),_kH=function(_kI,_kJ){return new F(function(){return A1(_kJ,_kG);});},_kK=new T(function(){return 0/0;}),_kL=function(_kM,_kN){return new F(function(){return A1(_kN,_kK);});},_kO=new T(function(){return B(unCStr("NaN"));}),_kP=new T(function(){return B(unCStr("Infinity"));}),_kQ=1024,_kR=-1021,_kS=new T(function(){return B(unCStr("base"));}),_kT=new T(function(){return B(unCStr("GHC.Exception"));}),_kU=new T(function(){return B(unCStr("ArithException"));}),_kV=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kS,_kT,_kU),_kW=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kV,_w,_w),_kX=function(_kY){return E(_kW);},_kZ=function(_l0){var _l1=E(_l0);return new F(function(){return _C(B(_A(_l1.a)),_kX,_l1.b);});},_l2=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_l3=new T(function(){return B(unCStr("denormal"));}),_l4=new T(function(){return B(unCStr("divide by zero"));}),_l5=new T(function(){return B(unCStr("loss of precision"));}),_l6=new T(function(){return B(unCStr("arithmetic underflow"));}),_l7=new T(function(){return B(unCStr("arithmetic overflow"));}),_l8=function(_l9,_la){switch(E(_l9)){case 0:return new F(function(){return _Q(_l7,_la);});break;case 1:return new F(function(){return _Q(_l6,_la);});break;case 2:return new F(function(){return _Q(_l5,_la);});break;case 3:return new F(function(){return _Q(_l4,_la);});break;case 4:return new F(function(){return _Q(_l3,_la);});break;default:return new F(function(){return _Q(_l2,_la);});}},_lb=function(_lc){return new F(function(){return _l8(_lc,_w);});},_ld=function(_le,_lf,_lg){return new F(function(){return _l8(_lf,_lg);});},_lh=function(_li,_lj){return new F(function(){return _1U(_l8,_li,_lj);});},_lk=new T3(0,_ld,_lb,_lh),_ll=new T(function(){return new T5(0,_kX,_lk,_lm,_kZ,_lb);}),_lm=function(_73){return new T2(0,_ll,_73);},_ln=3,_lo=new T(function(){return B(_lm(_ln));}),_lp=new T(function(){return die(_lo);}),_lq=function(_lr,_ls){var _lt=E(_lr);if(!_lt._){var _lu=_lt.a,_lv=E(_ls);return (_lv._==0)?_lu==_lv.a:(I_compareInt(_lv.a,_lu)==0)?true:false;}else{var _lw=_lt.a,_lx=E(_ls);return (_lx._==0)?(I_compareInt(_lw,_lx.a)==0)?true:false:(I_compare(_lw,_lx.a)==0)?true:false;}},_ly=new T1(0,0),_lz=function(_lA,_lB){while(1){var _lC=E(_lA);if(!_lC._){var _lD=E(_lC.a);if(_lD==(-2147483648)){_lA=new T1(1,I_fromInt(-2147483648));continue;}else{var _lE=E(_lB);if(!_lE._){return new T1(0,_lD%_lE.a);}else{_lA=new T1(1,I_fromInt(_lD));_lB=_lE;continue;}}}else{var _lF=_lC.a,_lG=E(_lB);return (_lG._==0)?new T1(1,I_rem(_lF,I_fromInt(_lG.a))):new T1(1,I_rem(_lF,_lG.a));}}},_lH=function(_lI,_lJ){if(!B(_lq(_lJ,_ly))){return new F(function(){return _lz(_lI,_lJ);});}else{return E(_lp);}},_lK=function(_lL,_lM){while(1){if(!B(_lq(_lM,_ly))){var _lN=_lM,_lO=B(_lH(_lL,_lM));_lL=_lN;_lM=_lO;continue;}else{return E(_lL);}}},_lP=function(_lQ){var _lR=E(_lQ);if(!_lR._){var _lS=E(_lR.a);return (_lS==(-2147483648))?E(_aQ):(_lS<0)?new T1(0, -_lS):E(_lR);}else{var _lT=_lR.a;return (I_compareInt(_lT,0)>=0)?E(_lR):new T1(1,I_negate(_lT));}},_lU=function(_lV,_lW){while(1){var _lX=E(_lV);if(!_lX._){var _lY=E(_lX.a);if(_lY==(-2147483648)){_lV=new T1(1,I_fromInt(-2147483648));continue;}else{var _lZ=E(_lW);if(!_lZ._){return new T1(0,quot(_lY,_lZ.a));}else{_lV=new T1(1,I_fromInt(_lY));_lW=_lZ;continue;}}}else{var _m0=_lX.a,_m1=E(_lW);return (_m1._==0)?new T1(0,I_toInt(I_quot(_m0,I_fromInt(_m1.a)))):new T1(1,I_quot(_m0,_m1.a));}}},_m2=5,_m3=new T(function(){return B(_lm(_m2));}),_m4=new T(function(){return die(_m3);}),_m5=function(_m6,_m7){if(!B(_lq(_m7,_ly))){var _m8=B(_lK(B(_lP(_m6)),B(_lP(_m7))));return (!B(_lq(_m8,_ly)))?new T2(0,B(_lU(_m6,_m8)),B(_lU(_m7,_m8))):E(_lp);}else{return E(_m4);}},_m9=new T1(0,1),_ma=new T(function(){return B(unCStr("Negative exponent"));}),_mb=new T(function(){return B(err(_ma));}),_mc=new T1(0,2),_md=new T(function(){return B(_lq(_mc,_ly));}),_me=function(_mf,_mg){while(1){var _mh=E(_mf);if(!_mh._){var _mi=_mh.a,_mj=E(_mg);if(!_mj._){var _mk=_mj.a,_ml=subC(_mi,_mk);if(!E(_ml.b)){return new T1(0,_ml.a);}else{_mf=new T1(1,I_fromInt(_mi));_mg=new T1(1,I_fromInt(_mk));continue;}}else{_mf=new T1(1,I_fromInt(_mi));_mg=_mj;continue;}}else{var _mm=E(_mg);if(!_mm._){_mf=_mh;_mg=new T1(1,I_fromInt(_mm.a));continue;}else{return new T1(1,I_sub(_mh.a,_mm.a));}}}},_mn=function(_mo,_mp,_mq){while(1){if(!E(_md)){if(!B(_lq(B(_lz(_mp,_mc)),_ly))){if(!B(_lq(_mp,_m9))){var _mr=B(_b7(_mo,_mo)),_ms=B(_lU(B(_me(_mp,_m9)),_mc)),_mt=B(_b7(_mo,_mq));_mo=_mr;_mp=_ms;_mq=_mt;continue;}else{return new F(function(){return _b7(_mo,_mq);});}}else{var _mr=B(_b7(_mo,_mo)),_ms=B(_lU(_mp,_mc));_mo=_mr;_mp=_ms;continue;}}else{return E(_lp);}}},_mu=function(_mv,_mw){while(1){if(!E(_md)){if(!B(_lq(B(_lz(_mw,_mc)),_ly))){if(!B(_lq(_mw,_m9))){return new F(function(){return _mn(B(_b7(_mv,_mv)),B(_lU(B(_me(_mw,_m9)),_mc)),_mv);});}else{return E(_mv);}}else{var _mx=B(_b7(_mv,_mv)),_my=B(_lU(_mw,_mc));_mv=_mx;_mw=_my;continue;}}else{return E(_lp);}}},_mz=function(_mA,_mB){var _mC=E(_mA);if(!_mC._){var _mD=_mC.a,_mE=E(_mB);return (_mE._==0)?_mD<_mE.a:I_compareInt(_mE.a,_mD)>0;}else{var _mF=_mC.a,_mG=E(_mB);return (_mG._==0)?I_compareInt(_mF,_mG.a)<0:I_compare(_mF,_mG.a)<0;}},_mH=function(_mI,_mJ){if(!B(_mz(_mJ,_ly))){if(!B(_lq(_mJ,_ly))){return new F(function(){return _mu(_mI,_mJ);});}else{return E(_m9);}}else{return E(_mb);}},_mK=new T1(0,1),_mL=new T1(0,0),_mM=new T1(0,-1),_mN=function(_mO){var _mP=E(_mO);if(!_mP._){var _mQ=_mP.a;return (_mQ>=0)?(E(_mQ)==0)?E(_mL):E(_aF):E(_mM);}else{var _mR=I_compareInt(_mP.a,0);return (_mR<=0)?(E(_mR)==0)?E(_mL):E(_mM):E(_aF);}},_mS=function(_mT,_mU,_mV){while(1){var _mW=E(_mV);if(!_mW._){if(!B(_mz(_mT,_bk))){return new T2(0,B(_b7(_mU,B(_mH(_aV,_mT)))),_m9);}else{var _mX=B(_mH(_aV,B(_aR(_mT))));return new F(function(){return _m5(B(_b7(_mU,B(_mN(_mX)))),B(_lP(_mX)));});}}else{var _mY=B(_me(_mT,_mK)),_mZ=B(_aH(B(_b7(_mU,_aV)),B(_b1(E(_mW.a)))));_mT=_mY;_mU=_mZ;_mV=_mW.b;continue;}}},_n0=function(_n1,_n2){var _n3=E(_n1);if(!_n3._){var _n4=_n3.a,_n5=E(_n2);return (_n5._==0)?_n4>=_n5.a:I_compareInt(_n5.a,_n4)<=0;}else{var _n6=_n3.a,_n7=E(_n2);return (_n7._==0)?I_compareInt(_n6,_n7.a)>=0:I_compare(_n6,_n7.a)>=0;}},_n8=function(_n9){var _na=E(_n9);if(!_na._){var _nb=_na.b;return new F(function(){return _m5(B(_b7(B(_bl(new T(function(){return B(_b1(E(_na.a)));}),new T(function(){return B(_aW(_nb,0));},1),B(_5y(_b3,_nb)))),_mK)),_mK);});}else{var _nc=_na.a,_nd=_na.c,_ne=E(_na.b);if(!_ne._){var _nf=E(_nd);if(!_nf._){return new F(function(){return _m5(B(_b7(B(_bC(_aV,_nc)),_mK)),_mK);});}else{var _ng=_nf.a;if(!B(_n0(_ng,_bk))){var _nh=B(_mH(_aV,B(_aR(_ng))));return new F(function(){return _m5(B(_b7(B(_bC(_aV,_nc)),B(_mN(_nh)))),B(_lP(_nh)));});}else{return new F(function(){return _m5(B(_b7(B(_b7(B(_bC(_aV,_nc)),B(_mH(_aV,_ng)))),_mK)),_mK);});}}}else{var _ni=_ne.a,_nj=E(_nd);if(!_nj._){return new F(function(){return _mS(_bk,B(_bC(_aV,_nc)),_ni);});}else{return new F(function(){return _mS(_nj.a,B(_bC(_aV,_nc)),_ni);});}}}},_nk=function(_nl,_nm){while(1){var _nn=E(_nm);if(!_nn._){return __Z;}else{if(!B(A1(_nl,_nn.a))){return E(_nn);}else{_nm=_nn.b;continue;}}}},_no=function(_np,_nq){var _nr=E(_np);if(!_nr._){var _ns=_nr.a,_nt=E(_nq);return (_nt._==0)?_ns>_nt.a:I_compareInt(_nt.a,_ns)<0;}else{var _nu=_nr.a,_nv=E(_nq);return (_nv._==0)?I_compareInt(_nu,_nv.a)>0:I_compare(_nu,_nv.a)>0;}},_nw=0,_nx=function(_ny,_nz){return E(_ny)==E(_nz);},_nA=function(_nB){return new F(function(){return _nx(_nw,_nB);});},_nC=new T2(0,E(_bk),E(_m9)),_nD=new T1(1,_nC),_nE=new T1(0,-2147483648),_nF=new T1(0,2147483647),_nG=function(_nH,_nI,_nJ){var _nK=E(_nJ);if(!_nK._){return new T1(1,new T(function(){var _nL=B(_n8(_nK));return new T2(0,E(_nL.a),E(_nL.b));}));}else{var _nM=E(_nK.c);if(!_nM._){return new T1(1,new T(function(){var _nN=B(_n8(_nK));return new T2(0,E(_nN.a),E(_nN.b));}));}else{var _nO=_nM.a;if(!B(_no(_nO,_nF))){if(!B(_mz(_nO,_nE))){var _nP=function(_nQ){var _nR=_nQ+B(_cH(_nO))|0;return (_nR<=(E(_nI)+3|0))?(_nR>=(E(_nH)-3|0))?new T1(1,new T(function(){var _nS=B(_n8(_nK));return new T2(0,E(_nS.a),E(_nS.b));})):E(_nD):__Z;},_nT=B(_nk(_nA,_nK.a));if(!_nT._){var _nU=E(_nK.b);if(!_nU._){return E(_nD);}else{var _nV=B(_74(_nA,_nU.a));if(!E(_nV.b)._){return E(_nD);}else{return new F(function(){return _nP( -B(_aW(_nV.a,0)));});}}}else{return new F(function(){return _nP(B(_aW(_nT,0)));});}}else{return __Z;}}else{return __Z;}}}},_nW=function(_nX,_nY){return new T0(2);},_nZ=new T1(0,1),_o0=function(_o1,_o2){var _o3=E(_o1);if(!_o3._){var _o4=_o3.a,_o5=E(_o2);if(!_o5._){var _o6=_o5.a;return (_o4!=_o6)?(_o4>_o6)?2:0:1;}else{var _o7=I_compareInt(_o5.a,_o4);return (_o7<=0)?(_o7>=0)?1:2:0;}}else{var _o8=_o3.a,_o9=E(_o2);if(!_o9._){var _oa=I_compareInt(_o8,_o9.a);return (_oa>=0)?(_oa<=0)?1:2:0;}else{var _ob=I_compare(_o8,_o9.a);return (_ob>=0)?(_ob<=0)?1:2:0;}}},_oc=function(_od,_oe){var _of=E(_od);return (_of._==0)?_of.a*Math.pow(2,_oe):I_toNumber(_of.a)*Math.pow(2,_oe);},_og=function(_oh,_oi){while(1){var _oj=E(_oh);if(!_oj._){var _ok=E(_oj.a);if(_ok==(-2147483648)){_oh=new T1(1,I_fromInt(-2147483648));continue;}else{var _ol=E(_oi);if(!_ol._){var _om=_ol.a;return new T2(0,new T1(0,quot(_ok,_om)),new T1(0,_ok%_om));}else{_oh=new T1(1,I_fromInt(_ok));_oi=_ol;continue;}}}else{var _on=E(_oi);if(!_on._){_oh=_oj;_oi=new T1(1,I_fromInt(_on.a));continue;}else{var _oo=I_quotRem(_oj.a,_on.a);return new T2(0,new T1(1,_oo.a),new T1(1,_oo.b));}}}},_op=new T1(0,0),_oq=function(_or,_os){while(1){var _ot=E(_or);if(!_ot._){_or=new T1(1,I_fromInt(_ot.a));continue;}else{return new T1(1,I_shiftLeft(_ot.a,_os));}}},_ou=function(_ov,_ow,_ox){if(!B(_lq(_ox,_op))){var _oy=B(_og(_ow,_ox)),_oz=_oy.a;switch(B(_o0(B(_oq(_oy.b,1)),_ox))){case 0:return new F(function(){return _oc(_oz,_ov);});break;case 1:if(!(B(_cH(_oz))&1)){return new F(function(){return _oc(_oz,_ov);});}else{return new F(function(){return _oc(B(_aH(_oz,_nZ)),_ov);});}break;default:return new F(function(){return _oc(B(_aH(_oz,_nZ)),_ov);});}}else{return E(_lp);}},_oA=function(_oB){var _oC=function(_oD,_oE){while(1){if(!B(_mz(_oD,_oB))){if(!B(_no(_oD,_oB))){if(!B(_lq(_oD,_oB))){return new F(function(){return _7q("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_oE);}}else{return _oE-1|0;}}else{var _oF=B(_oq(_oD,1)),_oG=_oE+1|0;_oD=_oF;_oE=_oG;continue;}}};return new F(function(){return _oC(_aF,0);});},_oH=function(_oI){var _oJ=E(_oI);if(!_oJ._){var _oK=_oJ.a>>>0;if(!_oK){return -1;}else{var _oL=function(_oM,_oN){while(1){if(_oM>=_oK){if(_oM<=_oK){if(_oM!=_oK){return new F(function(){return _7q("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_oN);}}else{return _oN-1|0;}}else{var _oO=imul(_oM,2)>>>0,_oP=_oN+1|0;_oM=_oO;_oN=_oP;continue;}}};return new F(function(){return _oL(1,0);});}}else{return new F(function(){return _oA(_oJ);});}},_oQ=function(_oR){var _oS=E(_oR);if(!_oS._){var _oT=_oS.a>>>0;if(!_oT){return new T2(0,-1,0);}else{var _oU=function(_oV,_oW){while(1){if(_oV>=_oT){if(_oV<=_oT){if(_oV!=_oT){return new F(function(){return _7q("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_oW);}}else{return _oW-1|0;}}else{var _oX=imul(_oV,2)>>>0,_oY=_oW+1|0;_oV=_oX;_oW=_oY;continue;}}};return new T2(0,B(_oU(1,0)),(_oT&_oT-1>>>0)>>>0&4294967295);}}else{var _oZ=_oS.a;return new T2(0,B(_oH(_oS)),I_compareInt(I_and(_oZ,I_sub(_oZ,I_fromInt(1))),0));}},_p0=function(_p1,_p2){while(1){var _p3=E(_p1);if(!_p3._){var _p4=_p3.a,_p5=E(_p2);if(!_p5._){return new T1(0,(_p4>>>0&_p5.a>>>0)>>>0&4294967295);}else{_p1=new T1(1,I_fromInt(_p4));_p2=_p5;continue;}}else{var _p6=E(_p2);if(!_p6._){_p1=_p3;_p2=new T1(1,I_fromInt(_p6.a));continue;}else{return new T1(1,I_and(_p3.a,_p6.a));}}}},_p7=new T1(0,2),_p8=function(_p9,_pa){var _pb=E(_p9);if(!_pb._){var _pc=(_pb.a>>>0&(2<<_pa>>>0)-1>>>0)>>>0,_pd=1<<_pa>>>0;return (_pd<=_pc)?(_pd>=_pc)?1:2:0;}else{var _pe=B(_p0(_pb,B(_me(B(_oq(_p7,_pa)),_aF)))),_pf=B(_oq(_aF,_pa));return (!B(_no(_pf,_pe)))?(!B(_mz(_pf,_pe)))?1:2:0;}},_pg=function(_ph,_pi){while(1){var _pj=E(_ph);if(!_pj._){_ph=new T1(1,I_fromInt(_pj.a));continue;}else{return new T1(1,I_shiftRight(_pj.a,_pi));}}},_pk=function(_pl,_pm,_pn,_po){var _pp=B(_oQ(_po)),_pq=_pp.a;if(!E(_pp.b)){var _pr=B(_oH(_pn));if(_pr<((_pq+_pl|0)-1|0)){var _ps=_pq+(_pl-_pm|0)|0;if(_ps>0){if(_ps>_pr){if(_ps<=(_pr+1|0)){if(!E(B(_oQ(_pn)).b)){return 0;}else{return new F(function(){return _oc(_nZ,_pl-_pm|0);});}}else{return 0;}}else{var _pt=B(_pg(_pn,_ps));switch(B(_p8(_pn,_ps-1|0))){case 0:return new F(function(){return _oc(_pt,_pl-_pm|0);});break;case 1:if(!(B(_cH(_pt))&1)){return new F(function(){return _oc(_pt,_pl-_pm|0);});}else{return new F(function(){return _oc(B(_aH(_pt,_nZ)),_pl-_pm|0);});}break;default:return new F(function(){return _oc(B(_aH(_pt,_nZ)),_pl-_pm|0);});}}}else{return new F(function(){return _oc(_pn,(_pl-_pm|0)-_ps|0);});}}else{if(_pr>=_pm){var _pu=B(_pg(_pn,(_pr+1|0)-_pm|0));switch(B(_p8(_pn,_pr-_pm|0))){case 0:return new F(function(){return _oc(_pu,((_pr-_pq|0)+1|0)-_pm|0);});break;case 2:return new F(function(){return _oc(B(_aH(_pu,_nZ)),((_pr-_pq|0)+1|0)-_pm|0);});break;default:if(!(B(_cH(_pu))&1)){return new F(function(){return _oc(_pu,((_pr-_pq|0)+1|0)-_pm|0);});}else{return new F(function(){return _oc(B(_aH(_pu,_nZ)),((_pr-_pq|0)+1|0)-_pm|0);});}}}else{return new F(function(){return _oc(_pn, -_pq);});}}}else{var _pv=B(_oH(_pn))-_pq|0,_pw=function(_px){var _py=function(_pz,_pA){if(!B(_cK(B(_oq(_pA,_pm)),_pz))){return new F(function(){return _ou(_px-_pm|0,_pz,_pA);});}else{return new F(function(){return _ou((_px-_pm|0)+1|0,_pz,B(_oq(_pA,1)));});}};if(_px>=_pm){if(_px!=_pm){return new F(function(){return _py(_pn,new T(function(){return B(_oq(_po,_px-_pm|0));}));});}else{return new F(function(){return _py(_pn,_po);});}}else{return new F(function(){return _py(new T(function(){return B(_oq(_pn,_pm-_px|0));}),_po);});}};if(_pl>_pv){return new F(function(){return _pw(_pl);});}else{return new F(function(){return _pw(_pv);});}}},_pB=new T(function(){return 0/0;}),_pC=new T(function(){return -1/0;}),_pD=new T(function(){return 1/0;}),_pE=0,_pF=function(_pG,_pH){if(!B(_lq(_pH,_op))){if(!B(_lq(_pG,_op))){if(!B(_mz(_pG,_op))){return new F(function(){return _pk(-1021,53,_pG,_pH);});}else{return  -B(_pk(-1021,53,B(_aR(_pG)),_pH));}}else{return E(_pE);}}else{return (!B(_lq(_pG,_op)))?(!B(_mz(_pG,_op)))?E(_pD):E(_pC):E(_pB);}},_pI=function(_pJ){var _pK=E(_pJ);switch(_pK._){case 3:var _pL=_pK.a;return (!B(_8h(_pL,_kP)))?(!B(_8h(_pL,_kO)))?E(_nW):E(_kL):E(_kH);case 5:var _pM=B(_nG(_kR,_kQ,_pK.a));if(!_pM._){return E(_kH);}else{var _pN=new T(function(){var _pO=E(_pM.a);return B(_pF(_pO.a,_pO.b));});return function(_pP,_pQ){return new F(function(){return A1(_pQ,_pN);});};}break;default:return E(_nW);}},_pR=function(_pS){var _pT=function(_pU){return E(new T2(3,_pS,_8N));};return new T1(1,function(_pV){return new F(function(){return A2(_i0,_pV,_pT);});});},_pW=new T(function(){return B(A3(_kl,_pI,_jQ,_pR));}),_pX=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_pY=function(_pZ){return new F(function(){return _71(new T1(0,new T(function(){return B(_7f(_pZ,_pX));})),_6L);});},_q0=new T(function(){return B(_pY("SMHI.hs:25:5-38|Str json"));}),_q1="value",_q2=function(_q3){while(1){var _q4=B((function(_q5){var _q6=E(_q5);if(!_q6._){return __Z;}else{var _q7=_q6.b,_q8=E(_q6.a);if(!E(_q8.b)._){return new T2(1,_q8.a,new T(function(){return B(_q2(_q7));}));}else{_q3=_q7;return __continue;}}})(_q3));if(_q4!=__continue){return _q4;}}},_q9=function(_qa,_qb){var _qc=E(_qb);if(!_qc._){return __Z;}else{var _qd=new T(function(){return B(_q9(new T(function(){return E(_qa)+1;}),_qc.b));}),_qe=new T(function(){var _qf=B(_q2(B(_7t(_pW,new T(function(){var _qg=B(_39(_qc.a,_q1));if(_qg._==1){return fromJSStr(_qg.a);}else{return E(_q0);}})))));if(!_qf._){return E(_6u);}else{if(!E(_qf.b)._){return E(_qf.a);}else{return E(_6w);}}});return new T2(1,new T2(0,_qa,_qe),_qd);}},_qh=new T(function(){return B(unCStr("http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/71420/period/latest-months/data.json"));}),_qi=new T(function(){return eval("(function(s){var x = eval(s);return (typeof x === \'undefined\') ? \'undefined\' : x.toString();})");}),_qj=function(_qk,_ql){while(1){var _qm=E(_qk);if(!_qm._){return E(_ql);}else{_qk=_qm.b;_ql=_qm.a;continue;}}},_qn=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_qo=function(_qp,_qq,_qr){var _qs=new T(function(){return toJSStr(E(_qr));});return function(_qt,_){var _qu=__app4(E(_qn),E(_qt),E(_qs),E(_qp),E(_qq));return new F(function(){return _49(_);});};},_qv=10,_qw=40,_qx=new T(function(){return B(unCStr("30\u00b0 C"));}),_qy=new T(function(){return B(_qo(_qv,_qw,_qx));}),_qz=new T(function(){return B(unCStr("last"));}),_qA=new T(function(){return B(_6o(_qz));}),_qB=new T(function(){return B(_pY("SMHI.hs:42:15-54|Num tstart"));}),_qC=new T3(0,128,128,128),_qD=",",_qE="rgba(",_qF=new T(function(){return toJSStr(_w);}),_qG="rgb(",_qH=")",_qI=new T2(1,_qH,_w),_qJ=function(_qK){var _qL=E(_qK);if(!_qL._){var _qM=jsCat(new T2(1,_qG,new T2(1,new T(function(){return String(_qL.a);}),new T2(1,_qD,new T2(1,new T(function(){return String(_qL.b);}),new T2(1,_qD,new T2(1,new T(function(){return String(_qL.c);}),_qI)))))),E(_qF));return E(_qM);}else{var _qN=jsCat(new T2(1,_qE,new T2(1,new T(function(){return String(_qL.a);}),new T2(1,_qD,new T2(1,new T(function(){return String(_qL.b);}),new T2(1,_qD,new T2(1,new T(function(){return String(_qL.c);}),new T2(1,_qD,new T2(1,new T(function(){return String(_qL.d);}),_qI)))))))),E(_qF));return E(_qN);}},_qO="fillStyle",_qP=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_qQ=function(_qR){var _qS=new T(function(){return B(_qJ(_qR));});return function(_qT,_){var _qU=__app3(E(_qP),E(_qT),E(_qO),E(_qS));return new F(function(){return _49(_);});};},_qV=new T(function(){return B(_qQ(_qC));}),_qW=new T(function(){return B(unCStr("); document.getElementById(\"title\").innerHTML = \"Hourly Temparature in Gothenburg from \" + start.toDateString() + \" \" + start.toTimeString() + \" to \" + end.toDateString() + \" \" + end.toTimeString();"));}),_qX=new T(function(){return eval("(function(x){console.log(x);})");}),_qY=function(_qZ,_r0){var _r1=function(_){var _r2=__app1(E(_qX),toJSStr(E(_r0)));return new F(function(){return _49(_);});};return new F(function(){return A2(_2D,_qZ,_r1);});},_r3=new T(function(){return B(_qY(_2u,_qh));}),_r4=new T(function(){return B(_pY("SMHI.hs:39:15-60|Arr dataPoints"));}),_r5=new T(function(){return B(_pY("SMHI.hs:45:15-50|Num tend"));}),_r6="date",_r7=new T3(0,0,0,0),_r8="strokeStyle",_r9=function(_ra){var _rb=new T(function(){return B(_qJ(_ra));});return function(_rc,_){var _rd=__app3(E(_qP),E(_rc),E(_r8),E(_rb));return new F(function(){return _49(_);});};},_re=new T(function(){return B(_r9(_r7));}),_rf=new T(function(){return B(_qQ(_r7));}),_rg=290,_rh=new T(function(){return B(unCStr("-20\u00b0 C"));}),_ri=new T(function(){return B(_qo(_qv,_rg,_rh));}),_rj=240,_rk=new T(function(){return B(unCStr("-10\u00b0 C"));}),_rl=new T(function(){return B(_qo(_qv,_rj,_rk));}),_rm=190,_rn=new T(function(){return B(unCStr("0\u00b0 C"));}),_ro=new T(function(){return B(_qo(_qv,_rm,_rn));}),_rp=140,_rq=new T(function(){return B(unCStr("10\u00b0 C"));}),_rr=new T(function(){return B(_qo(_qv,_rp,_rq));}),_rs=90,_rt=new T(function(){return B(unCStr("20\u00b0 C"));}),_ru=new T(function(){return B(_qo(_qv,_rs,_rt));}),_rv=300,_rw=function(_rx,_ry,_){while(1){var _rz=B((function(_rA,_rB,_){var _rC=E(_rA);if(!_rC._){return _2v;}else{var _rD=E(_rC.a),_rE=_rD.a,_rF=new T(function(){return E(_rE)+1;}),_rG=new T(function(){return 200-E(_rD.b)*5;}),_rH=B(_4H(new T2(1,new T2(0,_rE,_rv),new T2(1,new T2(0,_rF,_rv),new T2(1,new T2(0,_rF,_rG),new T2(1,new T2(0,_rE,_rG),new T2(1,new T2(0,_rE,_rv),_w))))),_rB,_)),_rI=_rB;_rx=_rC.b;_ry=_rI;return __continue;}})(_rx,_ry,_));if(_rz!=__continue){return _rz;}}},_rJ=function(_rK,_){var _rL=B(A1(_r3,_)),_rM=function(_rN,_){var _rO=E(_rN);if(!_rO._){return _2v;}else{var _rP=new T(function(){return B(_4B(800,new T(function(){var _rQ=B(_39(_rO.a,_q1));if(_rQ._==3){return E(_rQ.a);}else{return E(_r4);}},1)));}),_rR=new T(function(){var _rS=E(_rP);if(!_rS._){return E(_6r);}else{var _rT=B(_39(_rS.a,_r6));if(!_rT._){var _rU=jsShow(_rT.a),_rV=new T(function(){return B(unAppCStr(");var end = new Date (",new T(function(){var _rW=B(_39(B(_qj(_rS,_qA)),_r6));if(!_rW._){var _rX=jsShow(_rW.a);return B(_Q(fromJSStr(_rX),_qW));}else{return E(_r5);}})));},1);return B(_Q(fromJSStr(_rU),_rV));}else{return E(_qB);}}}),_rY=__app1(E(_qi),toJSStr(B(unAppCStr("var start = new Date(",_rR)))),_rZ=E(_rK),_s0=_rZ.a,_s1=__app1(E(_6s),_rZ.b),_s2=B(A2(_qV,_s0,_)),_s3=new T(function(){return B(_q9(_51,_rP));}),_s4=B(_4c(function(_s5,_){return new F(function(){return _rw(_s3,_s5,_);});},_s0,_)),_s6=B(A2(_re,_s0,_)),_s7=B(_4j(_5o,_s0,_)),_s8=B(A2(_rf,_s0,_)),_s9=B(A2(_ri,_s0,_)),_sa=B(A2(_rl,_s0,_)),_sb=B(A2(_ro,_s0,_)),_sc=B(A2(_rr,_s0,_)),_sd=B(A2(_ru,_s0,_));return new F(function(){return A2(_qy,_s0,_);});}};return new F(function(){return A(_5T,[_2u,_3n,_3n,_48,_4E,_qh,_w,_rM,_]);});},_se=function(_){var _sf=B(A3(_qY,_2u,_2N,_)),_sg=B(A3(_2F,_2u,_2M,_)),_sh=E(_sg);if(!_sh._){return new F(function(){return _2g(_2L,_);});}else{var _si=E(_sh.a),_sj=__app1(E(_1),_si);if(!_sj){return new F(function(){return _2g(_2L,_);});}else{var _sk=__app1(E(_0),_si),_sl=B(_rJ(new T2(0,_sk,_si),_));return _2v;}}},_sm=function(_){return new F(function(){return _se(_);});};
var hasteMain = function() {B(A(_sm, [0]));};window.onload = hasteMain;