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

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4,_){var _5=B(A1(_3,_)),_6=B(A1(_4,_));return _5;},_7=function(_8,_9,_){var _a=B(A1(_8,_)),_b=B(A1(_9,_));return new T(function(){return B(A1(_a,_b));});},_c=function(_d,_e,_){var _f=B(A1(_e,_));return _d;},_g=function(_h,_i,_){var _j=B(A1(_i,_));return new T(function(){return B(A1(_h,_j));});},_k=new T2(0,_g,_c),_l=function(_m,_){return _m;},_n=function(_o,_p,_){var _q=B(A1(_o,_));return new F(function(){return A1(_p,_);});},_r=new T5(0,_k,_l,_7,_n,_2),_s=new T(function(){return B(unCStr("base"));}),_t=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_u=new T(function(){return B(unCStr("IOException"));}),_v=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_s,_t,_u),_w=__Z,_x=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_v,_w,_w),_y=function(_z){return E(_x);},_A=function(_B){return E(E(_B).a);},_C=function(_D,_E,_F){var _G=B(A1(_D,_)),_H=B(A1(_E,_)),_I=hs_eqWord64(_G.a,_H.a);if(!_I){return __Z;}else{var _J=hs_eqWord64(_G.b,_H.b);return (!_J)?__Z:new T1(1,_F);}},_K=function(_L){var _M=E(_L);return new F(function(){return _C(B(_A(_M.a)),_y,_M.b);});},_N=new T(function(){return B(unCStr(": "));}),_O=new T(function(){return B(unCStr(")"));}),_P=new T(function(){return B(unCStr(" ("));}),_Q=function(_R,_S){var _T=E(_R);return (_T._==0)?E(_S):new T2(1,_T.a,new T(function(){return B(_Q(_T.b,_S));}));},_U=new T(function(){return B(unCStr("interrupted"));}),_V=new T(function(){return B(unCStr("system error"));}),_W=new T(function(){return B(unCStr("unsatisified constraints"));}),_X=new T(function(){return B(unCStr("user error"));}),_Y=new T(function(){return B(unCStr("permission denied"));}),_Z=new T(function(){return B(unCStr("illegal operation"));}),_10=new T(function(){return B(unCStr("end of file"));}),_11=new T(function(){return B(unCStr("resource exhausted"));}),_12=new T(function(){return B(unCStr("resource busy"));}),_13=new T(function(){return B(unCStr("does not exist"));}),_14=new T(function(){return B(unCStr("already exists"));}),_15=new T(function(){return B(unCStr("resource vanished"));}),_16=new T(function(){return B(unCStr("timeout"));}),_17=new T(function(){return B(unCStr("unsupported operation"));}),_18=new T(function(){return B(unCStr("hardware fault"));}),_19=new T(function(){return B(unCStr("inappropriate type"));}),_1a=new T(function(){return B(unCStr("invalid argument"));}),_1b=new T(function(){return B(unCStr("failed"));}),_1c=new T(function(){return B(unCStr("protocol error"));}),_1d=function(_1e,_1f){switch(E(_1e)){case 0:return new F(function(){return _Q(_14,_1f);});break;case 1:return new F(function(){return _Q(_13,_1f);});break;case 2:return new F(function(){return _Q(_12,_1f);});break;case 3:return new F(function(){return _Q(_11,_1f);});break;case 4:return new F(function(){return _Q(_10,_1f);});break;case 5:return new F(function(){return _Q(_Z,_1f);});break;case 6:return new F(function(){return _Q(_Y,_1f);});break;case 7:return new F(function(){return _Q(_X,_1f);});break;case 8:return new F(function(){return _Q(_W,_1f);});break;case 9:return new F(function(){return _Q(_V,_1f);});break;case 10:return new F(function(){return _Q(_1c,_1f);});break;case 11:return new F(function(){return _Q(_1b,_1f);});break;case 12:return new F(function(){return _Q(_1a,_1f);});break;case 13:return new F(function(){return _Q(_19,_1f);});break;case 14:return new F(function(){return _Q(_18,_1f);});break;case 15:return new F(function(){return _Q(_17,_1f);});break;case 16:return new F(function(){return _Q(_16,_1f);});break;case 17:return new F(function(){return _Q(_15,_1f);});break;default:return new F(function(){return _Q(_U,_1f);});}},_1g=new T(function(){return B(unCStr("}"));}),_1h=new T(function(){return B(unCStr("{handle: "));}),_1i=function(_1j,_1k,_1l,_1m,_1n,_1o){var _1p=new T(function(){var _1q=new T(function(){var _1r=new T(function(){var _1s=E(_1m);if(!_1s._){return E(_1o);}else{var _1t=new T(function(){return B(_Q(_1s,new T(function(){return B(_Q(_O,_1o));},1)));},1);return B(_Q(_P,_1t));}},1);return B(_1d(_1k,_1r));}),_1u=E(_1l);if(!_1u._){return E(_1q);}else{return B(_Q(_1u,new T(function(){return B(_Q(_N,_1q));},1)));}}),_1v=E(_1n);if(!_1v._){var _1w=E(_1j);if(!_1w._){return E(_1p);}else{var _1x=E(_1w.a);if(!_1x._){var _1y=new T(function(){var _1z=new T(function(){return B(_Q(_1g,new T(function(){return B(_Q(_N,_1p));},1)));},1);return B(_Q(_1x.a,_1z));},1);return new F(function(){return _Q(_1h,_1y);});}else{var _1A=new T(function(){var _1B=new T(function(){return B(_Q(_1g,new T(function(){return B(_Q(_N,_1p));},1)));},1);return B(_Q(_1x.a,_1B));},1);return new F(function(){return _Q(_1h,_1A);});}}}else{return new F(function(){return _Q(_1v.a,new T(function(){return B(_Q(_N,_1p));},1));});}},_1C=function(_1D){var _1E=E(_1D);return new F(function(){return _1i(_1E.a,_1E.b,_1E.c,_1E.d,_1E.f,_w);});},_1F=function(_1G){return new T2(0,_1H,_1G);},_1I=function(_1J,_1K,_1L){var _1M=E(_1K);return new F(function(){return _1i(_1M.a,_1M.b,_1M.c,_1M.d,_1M.f,_1L);});},_1N=function(_1O,_1P){var _1Q=E(_1O);return new F(function(){return _1i(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_1P);});},_1R=44,_1S=93,_1T=91,_1U=function(_1V,_1W,_1X){var _1Y=E(_1W);if(!_1Y._){return new F(function(){return unAppCStr("[]",_1X);});}else{var _1Z=new T(function(){var _20=new T(function(){var _21=function(_22){var _23=E(_22);if(!_23._){return E(new T2(1,_1S,_1X));}else{var _24=new T(function(){return B(A2(_1V,_23.a,new T(function(){return B(_21(_23.b));})));});return new T2(1,_1R,_24);}};return B(_21(_1Y.b));});return B(A2(_1V,_1Y.a,_20));});return new T2(1,_1T,_1Z);}},_25=function(_26,_27){return new F(function(){return _1U(_1N,_26,_27);});},_28=new T3(0,_1I,_1C,_25),_1H=new T(function(){return new T5(0,_y,_28,_1F,_K,_1C);}),_29=new T(function(){return E(_1H);}),_2a=function(_2b){return E(E(_2b).c);},_2c=__Z,_2d=7,_2e=function(_2f){return new T6(0,_2c,_2d,_w,_2f,_2c,_2c);},_2g=function(_2h,_){var _2i=new T(function(){return B(A2(_2a,_29,new T(function(){return B(A1(_2e,_2h));})));});return new F(function(){return die(_2i);});},_2j=function(_2k,_){return new F(function(){return _2g(_2k,_);});},_2l=function(_2m){return new F(function(){return A1(_2j,_2m);});},_2n=function(_2o,_2p,_){var _2q=B(A1(_2o,_));return new F(function(){return A2(_2p,_2q,_);});},_2r=new T5(0,_r,_2n,_n,_l,_2l),_2s=function(_2t){return E(_2t);},_2u=new T2(0,_2r,_2s),_2v=0,_2w=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2x=function(_){return new F(function(){return __jsNull();});},_2y=function(_2z){var _2A=B(A1(_2z,_));return E(_2A);},_2B=new T(function(){return B(_2y(_2x));}),_2C=new T(function(){return E(_2B);}),_2D=function(_2E){return E(E(_2E).b);},_2F=function(_2G,_2H){var _2I=function(_){var _2J=__app1(E(_2w),E(_2H)),_2K=__eq(_2J,E(_2C));return (E(_2K)==0)?new T1(1,_2J):_2c;};return new F(function(){return A2(_2D,_2G,_2I);});},_2L=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:9:5-15"));}),_2M="canvas",_2N=new T(function(){return B(unCStr("Starting"));}),_2O=function(_2P){return new F(function(){return err(B(unAppCStr("Haste.JSON.!: unable to look up key ",new T(function(){return fromJSStr(E(_2P));}))));});},_2Q=function(_2R){return E(E(_2R).a);},_2S=function(_2T,_2U){return (!B(A3(_2Q,_2V,_2T,_2U)))?true:false;},_2W=function(_2X,_2Y){var _2Z=strEq(E(_2X),E(_2Y));return (E(_2Z)==0)?false:true;},_30=function(_31,_32){return new F(function(){return _2W(_31,_32);});},_2V=new T(function(){return new T2(0,_30,_2S);}),_33=function(_34,_35,_36){while(1){var _37=E(_36);if(!_37._){return __Z;}else{var _38=E(_37.a);if(!B(A3(_2Q,_34,_35,_38.a))){_36=_37.b;continue;}else{return new T1(1,_38.b);}}}},_39=function(_3a,_3b){var _3c=E(_3a);if(_3c._==4){var _3d=B(_33(_2V,_3b,_3c.a));if(!_3d._){return new F(function(){return _2O(_3b);});}else{return E(_3d.a);}}else{return new F(function(){return _2O(_3b);});}},_3e=new T1(1,_2v),_3f="()",_3g=function(_3h){var _3i=strEq(_3h,E(_3f));return (E(_3i)==0)?__Z:E(_3e);},_3j=function(_3k){return new F(function(){return _3g(E(_3k));});},_3l=function(_3m){return E(_3f);},_3n=new T2(0,_3l,_3j),_3o=function(_3p){return new F(function(){return jsParseJSON(E(_3p));});},_3q="]",_3r="}",_3s=":",_3t=",",_3u=new T(function(){return eval("JSON.stringify");}),_3v="false",_3w="null",_3x="[",_3y="{",_3z="\"",_3A="true",_3B=function(_3C,_3D){var _3E=E(_3D);switch(_3E._){case 0:return new T2(0,new T(function(){return jsShow(_3E.a);}),_3C);case 1:return new T2(0,new T(function(){var _3F=__app1(E(_3u),_3E.a);return String(_3F);}),_3C);case 2:return (!E(_3E.a))?new T2(0,_3v,_3C):new T2(0,_3A,_3C);case 3:var _3G=E(_3E.a);if(!_3G._){return new T2(0,_3x,new T2(1,_3q,_3C));}else{var _3H=new T(function(){var _3I=new T(function(){var _3J=function(_3K){var _3L=E(_3K);if(!_3L._){return E(new T2(1,_3q,_3C));}else{var _3M=new T(function(){var _3N=B(_3B(new T(function(){return B(_3J(_3L.b));}),_3L.a));return new T2(1,_3N.a,_3N.b);});return new T2(1,_3t,_3M);}};return B(_3J(_3G.b));}),_3O=B(_3B(_3I,_3G.a));return new T2(1,_3O.a,_3O.b);});return new T2(0,_3x,_3H);}break;case 4:var _3P=E(_3E.a);if(!_3P._){return new T2(0,_3y,new T2(1,_3r,_3C));}else{var _3Q=E(_3P.a),_3R=new T(function(){var _3S=new T(function(){var _3T=function(_3U){var _3V=E(_3U);if(!_3V._){return E(new T2(1,_3r,_3C));}else{var _3W=E(_3V.a),_3X=new T(function(){var _3Y=B(_3B(new T(function(){return B(_3T(_3V.b));}),_3W.b));return new T2(1,_3Y.a,_3Y.b);});return new T2(1,_3t,new T2(1,_3z,new T2(1,_3W.a,new T2(1,_3z,new T2(1,_3s,_3X)))));}};return B(_3T(_3P.b));}),_3Z=B(_3B(_3S,_3Q.b));return new T2(1,_3Z.a,_3Z.b);});return new T2(0,_3y,new T2(1,new T(function(){var _40=__app1(E(_3u),E(_3Q.a));return String(_40);}),new T2(1,_3s,_3R)));}break;default:return new T2(0,_3w,_3C);}},_41=new T(function(){return toJSStr(_w);}),_42=function(_43){var _44=B(_3B(_w,_43)),_45=jsCat(new T2(1,_44.a,_44.b),E(_41));return E(_45);},_46=function(_47){return new F(function(){return _42(_47);});},_48=new T2(0,_46,_3o),_49=function(_){return _2v;},_4a=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_4b=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_4c=function(_4d,_4e,_){var _4f=__app1(E(_4a),_4e),_4g=B(A2(_4d,_4e,_)),_4h=__app1(E(_4b),_4e);return new F(function(){return _49(_);});},_4i=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_4j=function(_4k,_4l,_){var _4m=__app1(E(_4a),_4l),_4n=B(A2(_4k,_4l,_)),_4o=__app1(E(_4i),_4l);return new F(function(){return _49(_);});},_4p=function(_4q,_4r){var _4s=E(_4r);if(!_4s._){return __Z;}else{var _4t=_4s.a,_4u=E(_4q);return (_4u==1)?new T2(1,_4t,_w):new T2(1,_4t,new T(function(){return B(_4p(_4u-1|0,_4s.b));}));}},_4v=function(_4w,_4x){while(1){var _4y=E(_4w);if(!_4y._){return E(_4x);}else{var _4z=new T2(1,_4y.a,_4x);_4w=_4y.b;_4x=_4z;continue;}}},_4A=new T(function(){return B(_4v(_w,_w));}),_4B=function(_4C,_4D){if(0>=_4C){return E(_4A);}else{return new F(function(){return _4v(B(_4p(_4C,B(_4v(_4D,_w)))),_w);});}},_4E=0,_4F="POST",_4G="GET",_4H="=",_4I="&",_4J=function(_4K,_4L){var _4M=E(_4L);return (_4M._==0)?__Z:new T2(1,new T(function(){return B(A1(_4K,_4M.a));}),new T(function(){return B(_4J(_4K,_4M.b));}));},_4N=function(_4O){return E(E(_4O).a);},_4P=function(_4Q,_4R,_4S){var _4T=function(_4U){var _4V=E(_4U);return new F(function(){return jsCat(new T2(1,new T(function(){return B(A2(_4N,_4Q,_4V.a));}),new T2(1,new T(function(){return B(A2(_4N,_4R,_4V.b));}),_w)),E(_4H));});},_4W=jsCat(B(_4J(_4T,_4S)),E(_4I));return E(_4W);},_4X=new T(function(){return eval("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");}),_4Y=function(_4Z){return E(E(_4Z).b);},_50=new T(function(){return toJSStr(_w);}),_51="?",_52=function(_53){return new F(function(){return toJSStr(E(_53));});},_54=function(_55,_56,_57,_58,_59,_5a,_5b,_5c){var _5d=new T(function(){return B(_4P(_56,_57,_5b));}),_5e=new T(function(){return B(_52(_5a));}),_5f=function(_){var _5g=function(_5h){var _5i=function(_5j){var _5k=function(_5l){var _5m=new T(function(){return B(_4Y(_58));}),_5n=function(_5o,_){var _5p=new T(function(){var _5q=E(_5o),_5r=__eq(_5q,E(_2C));if(!E(_5r)){return B(A1(_5m,new T(function(){return String(_5q);})));}else{return __Z;}}),_5s=B(A2(_5c,_5p,_));return _2C;},_5t=__createJSFunc(2,E(_5n)),_5u=__app5(E(_4X),_5h,_5j,true,_5l,_5t);return _2v;};if(!E(_59)){return new F(function(){return _5k(E(_50));});}else{var _5v=E(_5b);if(!_5v._){return new F(function(){return _5k(E(_50));});}else{return new F(function(){return _5k(B(_4P(_56,_57,_5v)));});}}};if(!E(_59)){if(!E(_5b)._){return new F(function(){return _5i(toJSStr(E(_5a)));});}else{var _5w=jsCat(new T2(1,_5e,new T2(1,_5d,_w)),E(_51));return new F(function(){return _5i(_5w);});}}else{return new F(function(){return _5i(toJSStr(E(_5a)));});}};if(!E(_59)){return new F(function(){return _5g(E(_4G));});}else{return new F(function(){return _5g(E(_4F));});}};return new F(function(){return A2(_2D,_55,_5f);});},_5x=new T(function(){return eval("(function(e){e.width = e.width;})");}),_5y=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_5z=new T(function(){return B(err(_5y));}),_5A=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_5B=new T(function(){return B(err(_5A));}),_5C=new T(function(){return B(unCStr("base"));}),_5D=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5E=new T(function(){return B(unCStr("PatternMatchFail"));}),_5F=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5C,_5D,_5E),_5G=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5F,_w,_w),_5H=function(_5I){return E(_5G);},_5J=function(_5K){var _5L=E(_5K);return new F(function(){return _C(B(_A(_5L.a)),_5H,_5L.b);});},_5M=function(_5N){return E(E(_5N).a);},_5O=function(_5P){return new T2(0,_5Q,_5P);},_5R=function(_5S,_5T){return new F(function(){return _Q(E(_5S).a,_5T);});},_5U=function(_5V,_5W){return new F(function(){return _1U(_5R,_5V,_5W);});},_5X=function(_5Y,_5Z,_60){return new F(function(){return _Q(E(_5Z).a,_60);});},_61=new T3(0,_5X,_5M,_5U),_5Q=new T(function(){return new T5(0,_5H,_61,_5O,_5J,_5M);}),_62=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_63=function(_64,_65){return new F(function(){return die(new T(function(){return B(A2(_2a,_65,_64));}));});},_66=function(_67,_68){return new F(function(){return _63(_67,_68);});},_69=function(_6a,_6b){var _6c=E(_6b);if(!_6c._){return new T2(0,_w,_w);}else{var _6d=_6c.a;if(!B(A1(_6a,_6d))){return new T2(0,_w,_6c);}else{var _6e=new T(function(){var _6f=B(_69(_6a,_6c.b));return new T2(0,_6f.a,_6f.b);});return new T2(0,new T2(1,_6d,new T(function(){return E(E(_6e).a);})),new T(function(){return E(E(_6e).b);}));}}},_6g=32,_6h=new T(function(){return B(unCStr("\n"));}),_6i=function(_6j){return (E(_6j)==124)?false:true;},_6k=function(_6l,_6m){var _6n=B(_69(_6i,B(unCStr(_6l)))),_6o=_6n.a,_6p=function(_6q,_6r){var _6s=new T(function(){var _6t=new T(function(){return B(_Q(_6m,new T(function(){return B(_Q(_6r,_6h));},1)));});return B(unAppCStr(": ",_6t));},1);return new F(function(){return _Q(_6q,_6s);});},_6u=E(_6n.b);if(!_6u._){return new F(function(){return _6p(_6o,_w);});}else{if(E(_6u.a)==124){return new F(function(){return _6p(_6o,new T2(1,_6g,_6u.b));});}else{return new F(function(){return _6p(_6o,_w);});}}},_6v=function(_6w){return new F(function(){return _66(new T1(0,new T(function(){return B(_6k(_6w,_62));})),_5Q);});},_6x=new T(function(){return B(_6v("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_6y=function(_6z,_6A){while(1){var _6B=B((function(_6C,_6D){var _6E=E(_6C);switch(_6E._){case 0:var _6F=E(_6D);if(!_6F._){return __Z;}else{_6z=B(A1(_6E.a,_6F.a));_6A=_6F.b;return __continue;}break;case 1:var _6G=B(A1(_6E.a,_6D)),_6H=_6D;_6z=_6G;_6A=_6H;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_6E.a,_6D),new T(function(){return B(_6y(_6E.b,_6D));}));default:return E(_6E.a);}})(_6z,_6A));if(_6B!=__continue){return _6B;}}},_6I=function(_6J,_6K){var _6L=function(_6M){var _6N=E(_6K);if(_6N._==3){return new T2(3,_6N.a,new T(function(){return B(_6I(_6J,_6N.b));}));}else{var _6O=E(_6J);if(_6O._==2){return E(_6N);}else{var _6P=E(_6N);if(_6P._==2){return E(_6O);}else{var _6Q=function(_6R){var _6S=E(_6P);if(_6S._==4){var _6T=function(_6U){return new T1(4,new T(function(){return B(_Q(B(_6y(_6O,_6U)),_6S.a));}));};return new T1(1,_6T);}else{var _6V=E(_6O);if(_6V._==1){var _6W=_6V.a,_6X=E(_6S);if(!_6X._){return new T1(1,function(_6Y){return new F(function(){return _6I(B(A1(_6W,_6Y)),_6X);});});}else{var _6Z=function(_70){return new F(function(){return _6I(B(A1(_6W,_70)),new T(function(){return B(A1(_6X.a,_70));}));});};return new T1(1,_6Z);}}else{var _71=E(_6S);if(!_71._){return E(_6x);}else{var _72=function(_73){return new F(function(){return _6I(_6V,new T(function(){return B(A1(_71.a,_73));}));});};return new T1(1,_72);}}}},_74=E(_6O);switch(_74._){case 1:var _75=E(_6P);if(_75._==4){var _76=function(_77){return new T1(4,new T(function(){return B(_Q(B(_6y(B(A1(_74.a,_77)),_77)),_75.a));}));};return new T1(1,_76);}else{return new F(function(){return _6Q(_);});}break;case 4:var _78=_74.a,_79=E(_6P);switch(_79._){case 0:var _7a=function(_7b){var _7c=new T(function(){return B(_Q(_78,new T(function(){return B(_6y(_79,_7b));},1)));});return new T1(4,_7c);};return new T1(1,_7a);case 1:var _7d=function(_7e){var _7f=new T(function(){return B(_Q(_78,new T(function(){return B(_6y(B(A1(_79.a,_7e)),_7e));},1)));});return new T1(4,_7f);};return new T1(1,_7d);default:return new T1(4,new T(function(){return B(_Q(_78,_79.a));}));}break;default:return new F(function(){return _6Q(_);});}}}}},_7g=E(_6J);switch(_7g._){case 0:var _7h=E(_6K);if(!_7h._){var _7i=function(_7j){return new F(function(){return _6I(B(A1(_7g.a,_7j)),new T(function(){return B(A1(_7h.a,_7j));}));});};return new T1(0,_7i);}else{return new F(function(){return _6L(_);});}break;case 3:return new T2(3,_7g.a,new T(function(){return B(_6I(_7g.b,_6K));}));default:return new F(function(){return _6L(_);});}},_7k=new T(function(){return B(unCStr("("));}),_7l=new T(function(){return B(unCStr(")"));}),_7m=function(_7n,_7o){while(1){var _7p=E(_7n);if(!_7p._){return (E(_7o)._==0)?true:false;}else{var _7q=E(_7o);if(!_7q._){return false;}else{if(E(_7p.a)!=E(_7q.a)){return false;}else{_7n=_7p.b;_7o=_7q.b;continue;}}}}},_7r=function(_7s,_7t){return E(_7s)!=E(_7t);},_7u=function(_7v,_7w){return E(_7v)==E(_7w);},_7x=new T2(0,_7u,_7r),_7y=function(_7z,_7A){while(1){var _7B=E(_7z);if(!_7B._){return (E(_7A)._==0)?true:false;}else{var _7C=E(_7A);if(!_7C._){return false;}else{if(E(_7B.a)!=E(_7C.a)){return false;}else{_7z=_7B.b;_7A=_7C.b;continue;}}}}},_7D=function(_7E,_7F){return (!B(_7y(_7E,_7F)))?true:false;},_7G=new T2(0,_7y,_7D),_7H=function(_7I,_7J){var _7K=E(_7I);switch(_7K._){case 0:return new T1(0,function(_7L){return new F(function(){return _7H(B(A1(_7K.a,_7L)),_7J);});});case 1:return new T1(1,function(_7M){return new F(function(){return _7H(B(A1(_7K.a,_7M)),_7J);});});case 2:return new T0(2);case 3:return new F(function(){return _6I(B(A1(_7J,_7K.a)),new T(function(){return B(_7H(_7K.b,_7J));}));});break;default:var _7N=function(_7O){var _7P=E(_7O);if(!_7P._){return __Z;}else{var _7Q=E(_7P.a);return new F(function(){return _Q(B(_6y(B(A1(_7J,_7Q.a)),_7Q.b)),new T(function(){return B(_7N(_7P.b));},1));});}},_7R=B(_7N(_7K.a));return (_7R._==0)?new T0(2):new T1(4,_7R);}},_7S=new T0(2),_7T=function(_7U){return new T2(3,_7U,_7S);},_7V=function(_7W,_7X){var _7Y=E(_7W);if(!_7Y){return new F(function(){return A1(_7X,_2v);});}else{var _7Z=new T(function(){return B(_7V(_7Y-1|0,_7X));});return new T1(0,function(_80){return E(_7Z);});}},_81=function(_82,_83,_84){var _85=new T(function(){return B(A1(_82,_7T));}),_86=function(_87,_88,_89,_8a){while(1){var _8b=B((function(_8c,_8d,_8e,_8f){var _8g=E(_8c);switch(_8g._){case 0:var _8h=E(_8d);if(!_8h._){return new F(function(){return A1(_83,_8f);});}else{var _8i=_8e+1|0,_8j=_8f;_87=B(A1(_8g.a,_8h.a));_88=_8h.b;_89=_8i;_8a=_8j;return __continue;}break;case 1:var _8k=B(A1(_8g.a,_8d)),_8l=_8d,_8i=_8e,_8j=_8f;_87=_8k;_88=_8l;_89=_8i;_8a=_8j;return __continue;case 2:return new F(function(){return A1(_83,_8f);});break;case 3:var _8m=new T(function(){return B(_7H(_8g,_8f));});return new F(function(){return _7V(_8e,function(_8n){return E(_8m);});});break;default:return new F(function(){return _7H(_8g,_8f);});}})(_87,_88,_89,_8a));if(_8b!=__continue){return _8b;}}};return function(_8o){return new F(function(){return _86(_85,_8o,0,_84);});};},_8p=function(_8q){return new F(function(){return A1(_8q,_w);});},_8r=function(_8s,_8t){var _8u=function(_8v){var _8w=E(_8v);if(!_8w._){return E(_8p);}else{var _8x=_8w.a;if(!B(A1(_8s,_8x))){return E(_8p);}else{var _8y=new T(function(){return B(_8u(_8w.b));}),_8z=function(_8A){var _8B=new T(function(){return B(A1(_8y,function(_8C){return new F(function(){return A1(_8A,new T2(1,_8x,_8C));});}));});return new T1(0,function(_8D){return E(_8B);});};return E(_8z);}}};return function(_8E){return new F(function(){return A2(_8u,_8E,_8t);});};},_8F=new T0(6),_8G=new T(function(){return B(unCStr("valDig: Bad base"));}),_8H=new T(function(){return B(err(_8G));}),_8I=function(_8J,_8K){var _8L=function(_8M,_8N){var _8O=E(_8M);if(!_8O._){var _8P=new T(function(){return B(A1(_8N,_w));});return function(_8Q){return new F(function(){return A1(_8Q,_8P);});};}else{var _8R=E(_8O.a),_8S=function(_8T){var _8U=new T(function(){return B(_8L(_8O.b,function(_8V){return new F(function(){return A1(_8N,new T2(1,_8T,_8V));});}));}),_8W=function(_8X){var _8Y=new T(function(){return B(A1(_8U,_8X));});return new T1(0,function(_8Z){return E(_8Y);});};return E(_8W);};switch(E(_8J)){case 8:if(48>_8R){var _90=new T(function(){return B(A1(_8N,_w));});return function(_91){return new F(function(){return A1(_91,_90);});};}else{if(_8R>55){var _92=new T(function(){return B(A1(_8N,_w));});return function(_93){return new F(function(){return A1(_93,_92);});};}else{return new F(function(){return _8S(_8R-48|0);});}}break;case 10:if(48>_8R){var _94=new T(function(){return B(A1(_8N,_w));});return function(_95){return new F(function(){return A1(_95,_94);});};}else{if(_8R>57){var _96=new T(function(){return B(A1(_8N,_w));});return function(_97){return new F(function(){return A1(_97,_96);});};}else{return new F(function(){return _8S(_8R-48|0);});}}break;case 16:if(48>_8R){if(97>_8R){if(65>_8R){var _98=new T(function(){return B(A1(_8N,_w));});return function(_99){return new F(function(){return A1(_99,_98);});};}else{if(_8R>70){var _9a=new T(function(){return B(A1(_8N,_w));});return function(_9b){return new F(function(){return A1(_9b,_9a);});};}else{return new F(function(){return _8S((_8R-65|0)+10|0);});}}}else{if(_8R>102){if(65>_8R){var _9c=new T(function(){return B(A1(_8N,_w));});return function(_9d){return new F(function(){return A1(_9d,_9c);});};}else{if(_8R>70){var _9e=new T(function(){return B(A1(_8N,_w));});return function(_9f){return new F(function(){return A1(_9f,_9e);});};}else{return new F(function(){return _8S((_8R-65|0)+10|0);});}}}else{return new F(function(){return _8S((_8R-97|0)+10|0);});}}}else{if(_8R>57){if(97>_8R){if(65>_8R){var _9g=new T(function(){return B(A1(_8N,_w));});return function(_9h){return new F(function(){return A1(_9h,_9g);});};}else{if(_8R>70){var _9i=new T(function(){return B(A1(_8N,_w));});return function(_9j){return new F(function(){return A1(_9j,_9i);});};}else{return new F(function(){return _8S((_8R-65|0)+10|0);});}}}else{if(_8R>102){if(65>_8R){var _9k=new T(function(){return B(A1(_8N,_w));});return function(_9l){return new F(function(){return A1(_9l,_9k);});};}else{if(_8R>70){var _9m=new T(function(){return B(A1(_8N,_w));});return function(_9n){return new F(function(){return A1(_9n,_9m);});};}else{return new F(function(){return _8S((_8R-65|0)+10|0);});}}}else{return new F(function(){return _8S((_8R-97|0)+10|0);});}}}else{return new F(function(){return _8S(_8R-48|0);});}}break;default:return E(_8H);}}},_9o=function(_9p){var _9q=E(_9p);if(!_9q._){return new T0(2);}else{return new F(function(){return A1(_8K,_9q);});}};return function(_9r){return new F(function(){return A3(_8L,_9r,_2s,_9o);});};},_9s=16,_9t=8,_9u=function(_9v){var _9w=function(_9x){return new F(function(){return A1(_9v,new T1(5,new T2(0,_9t,_9x)));});},_9y=function(_9z){return new F(function(){return A1(_9v,new T1(5,new T2(0,_9s,_9z)));});},_9A=function(_9B){switch(E(_9B)){case 79:return new T1(1,B(_8I(_9t,_9w)));case 88:return new T1(1,B(_8I(_9s,_9y)));case 111:return new T1(1,B(_8I(_9t,_9w)));case 120:return new T1(1,B(_8I(_9s,_9y)));default:return new T0(2);}};return function(_9C){return (E(_9C)==48)?E(new T1(0,_9A)):new T0(2);};},_9D=function(_9E){return new T1(0,B(_9u(_9E)));},_9F=function(_9G){return new F(function(){return A1(_9G,_2c);});},_9H=function(_9I){return new F(function(){return A1(_9I,_2c);});},_9J=10,_9K=new T1(0,1),_9L=new T1(0,2147483647),_9M=function(_9N,_9O){while(1){var _9P=E(_9N);if(!_9P._){var _9Q=_9P.a,_9R=E(_9O);if(!_9R._){var _9S=_9R.a,_9T=addC(_9Q,_9S);if(!E(_9T.b)){return new T1(0,_9T.a);}else{_9N=new T1(1,I_fromInt(_9Q));_9O=new T1(1,I_fromInt(_9S));continue;}}else{_9N=new T1(1,I_fromInt(_9Q));_9O=_9R;continue;}}else{var _9U=E(_9O);if(!_9U._){_9N=_9P;_9O=new T1(1,I_fromInt(_9U.a));continue;}else{return new T1(1,I_add(_9P.a,_9U.a));}}}},_9V=new T(function(){return B(_9M(_9L,_9K));}),_9W=function(_9X){var _9Y=E(_9X);if(!_9Y._){var _9Z=E(_9Y.a);return (_9Z==(-2147483648))?E(_9V):new T1(0, -_9Z);}else{return new T1(1,I_negate(_9Y.a));}},_a0=new T1(0,10),_a1=function(_a2,_a3){while(1){var _a4=E(_a2);if(!_a4._){return E(_a3);}else{var _a5=_a3+1|0;_a2=_a4.b;_a3=_a5;continue;}}},_a6=function(_a7){return new T1(0,_a7);},_a8=function(_a9){return new F(function(){return _a6(E(_a9));});},_aa=new T(function(){return B(unCStr("this should not happen"));}),_ab=new T(function(){return B(err(_aa));}),_ac=function(_ad,_ae){while(1){var _af=E(_ad);if(!_af._){var _ag=_af.a,_ah=E(_ae);if(!_ah._){var _ai=_ah.a;if(!(imul(_ag,_ai)|0)){return new T1(0,imul(_ag,_ai)|0);}else{_ad=new T1(1,I_fromInt(_ag));_ae=new T1(1,I_fromInt(_ai));continue;}}else{_ad=new T1(1,I_fromInt(_ag));_ae=_ah;continue;}}else{var _aj=E(_ae);if(!_aj._){_ad=_af;_ae=new T1(1,I_fromInt(_aj.a));continue;}else{return new T1(1,I_mul(_af.a,_aj.a));}}}},_ak=function(_al,_am){var _an=E(_am);if(!_an._){return __Z;}else{var _ao=E(_an.b);return (_ao._==0)?E(_ab):new T2(1,B(_9M(B(_ac(_an.a,_al)),_ao.a)),new T(function(){return B(_ak(_al,_ao.b));}));}},_ap=new T1(0,0),_aq=function(_ar,_as,_at){while(1){var _au=B((function(_av,_aw,_ax){var _ay=E(_ax);if(!_ay._){return E(_ap);}else{if(!E(_ay.b)._){return E(_ay.a);}else{var _az=E(_aw);if(_az<=40){var _aA=function(_aB,_aC){while(1){var _aD=E(_aC);if(!_aD._){return E(_aB);}else{var _aE=B(_9M(B(_ac(_aB,_av)),_aD.a));_aB=_aE;_aC=_aD.b;continue;}}};return new F(function(){return _aA(_ap,_ay);});}else{var _aF=B(_ac(_av,_av));if(!(_az%2)){var _aG=B(_ak(_av,_ay));_ar=_aF;_as=quot(_az+1|0,2);_at=_aG;return __continue;}else{var _aG=B(_ak(_av,new T2(1,_ap,_ay)));_ar=_aF;_as=quot(_az+1|0,2);_at=_aG;return __continue;}}}}})(_ar,_as,_at));if(_au!=__continue){return _au;}}},_aH=function(_aI,_aJ){return new F(function(){return _aq(_aI,new T(function(){return B(_a1(_aJ,0));},1),B(_4J(_a8,_aJ)));});},_aK=function(_aL){var _aM=new T(function(){var _aN=new T(function(){var _aO=function(_aP){return new F(function(){return A1(_aL,new T1(1,new T(function(){return B(_aH(_a0,_aP));})));});};return new T1(1,B(_8I(_9J,_aO)));}),_aQ=function(_aR){if(E(_aR)==43){var _aS=function(_aT){return new F(function(){return A1(_aL,new T1(1,new T(function(){return B(_aH(_a0,_aT));})));});};return new T1(1,B(_8I(_9J,_aS)));}else{return new T0(2);}},_aU=function(_aV){if(E(_aV)==45){var _aW=function(_aX){return new F(function(){return A1(_aL,new T1(1,new T(function(){return B(_9W(B(_aH(_a0,_aX))));})));});};return new T1(1,B(_8I(_9J,_aW)));}else{return new T0(2);}};return B(_6I(B(_6I(new T1(0,_aU),new T1(0,_aQ))),_aN));});return new F(function(){return _6I(new T1(0,function(_aY){return (E(_aY)==101)?E(_aM):new T0(2);}),new T1(0,function(_aZ){return (E(_aZ)==69)?E(_aM):new T0(2);}));});},_b0=function(_b1){var _b2=function(_b3){return new F(function(){return A1(_b1,new T1(1,_b3));});};return function(_b4){return (E(_b4)==46)?new T1(1,B(_8I(_9J,_b2))):new T0(2);};},_b5=function(_b6){return new T1(0,B(_b0(_b6)));},_b7=function(_b8){var _b9=function(_ba){var _bb=function(_bc){return new T1(1,B(_81(_aK,_9F,function(_bd){return new F(function(){return A1(_b8,new T1(5,new T3(1,_ba,_bc,_bd)));});})));};return new T1(1,B(_81(_b5,_9H,_bb)));};return new F(function(){return _8I(_9J,_b9);});},_be=function(_bf){return new T1(1,B(_b7(_bf)));},_bg=function(_bh,_bi,_bj){while(1){var _bk=E(_bj);if(!_bk._){return false;}else{if(!B(A3(_2Q,_bh,_bi,_bk.a))){_bj=_bk.b;continue;}else{return true;}}}},_bl=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_bm=function(_bn){return new F(function(){return _bg(_7x,_bn,_bl);});},_bo=false,_bp=true,_bq=function(_br){var _bs=new T(function(){return B(A1(_br,_9t));}),_bt=new T(function(){return B(A1(_br,_9s));});return function(_bu){switch(E(_bu)){case 79:return E(_bs);case 88:return E(_bt);case 111:return E(_bs);case 120:return E(_bt);default:return new T0(2);}};},_bv=function(_bw){return new T1(0,B(_bq(_bw)));},_bx=function(_by){return new F(function(){return A1(_by,_9J);});},_bz=function(_bA,_bB){var _bC=jsShowI(_bA);return new F(function(){return _Q(fromJSStr(_bC),_bB);});},_bD=41,_bE=40,_bF=function(_bG,_bH,_bI){if(_bH>=0){return new F(function(){return _bz(_bH,_bI);});}else{if(_bG<=6){return new F(function(){return _bz(_bH,_bI);});}else{return new T2(1,_bE,new T(function(){var _bJ=jsShowI(_bH);return B(_Q(fromJSStr(_bJ),new T2(1,_bD,_bI)));}));}}},_bK=function(_bL){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_bF(9,_bL,_w));}))));});},_bM=function(_bN){var _bO=E(_bN);if(!_bO._){return E(_bO.a);}else{return new F(function(){return I_toInt(_bO.a);});}},_bP=function(_bQ,_bR){var _bS=E(_bQ);if(!_bS._){var _bT=_bS.a,_bU=E(_bR);return (_bU._==0)?_bT<=_bU.a:I_compareInt(_bU.a,_bT)>=0;}else{var _bV=_bS.a,_bW=E(_bR);return (_bW._==0)?I_compareInt(_bV,_bW.a)<=0:I_compare(_bV,_bW.a)<=0;}},_bX=function(_bY){return new T0(2);},_bZ=function(_c0){var _c1=E(_c0);if(!_c1._){return E(_bX);}else{var _c2=_c1.a,_c3=E(_c1.b);if(!_c3._){return E(_c2);}else{var _c4=new T(function(){return B(_bZ(_c3));}),_c5=function(_c6){return new F(function(){return _6I(B(A1(_c2,_c6)),new T(function(){return B(A1(_c4,_c6));}));});};return E(_c5);}}},_c7=function(_c8,_c9){var _ca=function(_cb,_cc,_cd){var _ce=E(_cb);if(!_ce._){return new F(function(){return A1(_cd,_c8);});}else{var _cf=E(_cc);if(!_cf._){return new T0(2);}else{if(E(_ce.a)!=E(_cf.a)){return new T0(2);}else{var _cg=new T(function(){return B(_ca(_ce.b,_cf.b,_cd));});return new T1(0,function(_ch){return E(_cg);});}}}};return function(_ci){return new F(function(){return _ca(_c8,_ci,_c9);});};},_cj=new T(function(){return B(unCStr("SO"));}),_ck=14,_cl=function(_cm){var _cn=new T(function(){return B(A1(_cm,_ck));});return new T1(1,B(_c7(_cj,function(_co){return E(_cn);})));},_cp=new T(function(){return B(unCStr("SOH"));}),_cq=1,_cr=function(_cs){var _ct=new T(function(){return B(A1(_cs,_cq));});return new T1(1,B(_c7(_cp,function(_cu){return E(_ct);})));},_cv=function(_cw){return new T1(1,B(_81(_cr,_cl,_cw)));},_cx=new T(function(){return B(unCStr("NUL"));}),_cy=0,_cz=function(_cA){var _cB=new T(function(){return B(A1(_cA,_cy));});return new T1(1,B(_c7(_cx,function(_cC){return E(_cB);})));},_cD=new T(function(){return B(unCStr("STX"));}),_cE=2,_cF=function(_cG){var _cH=new T(function(){return B(A1(_cG,_cE));});return new T1(1,B(_c7(_cD,function(_cI){return E(_cH);})));},_cJ=new T(function(){return B(unCStr("ETX"));}),_cK=3,_cL=function(_cM){var _cN=new T(function(){return B(A1(_cM,_cK));});return new T1(1,B(_c7(_cJ,function(_cO){return E(_cN);})));},_cP=new T(function(){return B(unCStr("EOT"));}),_cQ=4,_cR=function(_cS){var _cT=new T(function(){return B(A1(_cS,_cQ));});return new T1(1,B(_c7(_cP,function(_cU){return E(_cT);})));},_cV=new T(function(){return B(unCStr("ENQ"));}),_cW=5,_cX=function(_cY){var _cZ=new T(function(){return B(A1(_cY,_cW));});return new T1(1,B(_c7(_cV,function(_d0){return E(_cZ);})));},_d1=new T(function(){return B(unCStr("ACK"));}),_d2=6,_d3=function(_d4){var _d5=new T(function(){return B(A1(_d4,_d2));});return new T1(1,B(_c7(_d1,function(_d6){return E(_d5);})));},_d7=new T(function(){return B(unCStr("BEL"));}),_d8=7,_d9=function(_da){var _db=new T(function(){return B(A1(_da,_d8));});return new T1(1,B(_c7(_d7,function(_dc){return E(_db);})));},_dd=new T(function(){return B(unCStr("BS"));}),_de=8,_df=function(_dg){var _dh=new T(function(){return B(A1(_dg,_de));});return new T1(1,B(_c7(_dd,function(_di){return E(_dh);})));},_dj=new T(function(){return B(unCStr("HT"));}),_dk=9,_dl=function(_dm){var _dn=new T(function(){return B(A1(_dm,_dk));});return new T1(1,B(_c7(_dj,function(_do){return E(_dn);})));},_dp=new T(function(){return B(unCStr("LF"));}),_dq=10,_dr=function(_ds){var _dt=new T(function(){return B(A1(_ds,_dq));});return new T1(1,B(_c7(_dp,function(_du){return E(_dt);})));},_dv=new T(function(){return B(unCStr("VT"));}),_dw=11,_dx=function(_dy){var _dz=new T(function(){return B(A1(_dy,_dw));});return new T1(1,B(_c7(_dv,function(_dA){return E(_dz);})));},_dB=new T(function(){return B(unCStr("FF"));}),_dC=12,_dD=function(_dE){var _dF=new T(function(){return B(A1(_dE,_dC));});return new T1(1,B(_c7(_dB,function(_dG){return E(_dF);})));},_dH=new T(function(){return B(unCStr("CR"));}),_dI=13,_dJ=function(_dK){var _dL=new T(function(){return B(A1(_dK,_dI));});return new T1(1,B(_c7(_dH,function(_dM){return E(_dL);})));},_dN=new T(function(){return B(unCStr("SI"));}),_dO=15,_dP=function(_dQ){var _dR=new T(function(){return B(A1(_dQ,_dO));});return new T1(1,B(_c7(_dN,function(_dS){return E(_dR);})));},_dT=new T(function(){return B(unCStr("DLE"));}),_dU=16,_dV=function(_dW){var _dX=new T(function(){return B(A1(_dW,_dU));});return new T1(1,B(_c7(_dT,function(_dY){return E(_dX);})));},_dZ=new T(function(){return B(unCStr("DC1"));}),_e0=17,_e1=function(_e2){var _e3=new T(function(){return B(A1(_e2,_e0));});return new T1(1,B(_c7(_dZ,function(_e4){return E(_e3);})));},_e5=new T(function(){return B(unCStr("DC2"));}),_e6=18,_e7=function(_e8){var _e9=new T(function(){return B(A1(_e8,_e6));});return new T1(1,B(_c7(_e5,function(_ea){return E(_e9);})));},_eb=new T(function(){return B(unCStr("DC3"));}),_ec=19,_ed=function(_ee){var _ef=new T(function(){return B(A1(_ee,_ec));});return new T1(1,B(_c7(_eb,function(_eg){return E(_ef);})));},_eh=new T(function(){return B(unCStr("DC4"));}),_ei=20,_ej=function(_ek){var _el=new T(function(){return B(A1(_ek,_ei));});return new T1(1,B(_c7(_eh,function(_em){return E(_el);})));},_en=new T(function(){return B(unCStr("NAK"));}),_eo=21,_ep=function(_eq){var _er=new T(function(){return B(A1(_eq,_eo));});return new T1(1,B(_c7(_en,function(_es){return E(_er);})));},_et=new T(function(){return B(unCStr("SYN"));}),_eu=22,_ev=function(_ew){var _ex=new T(function(){return B(A1(_ew,_eu));});return new T1(1,B(_c7(_et,function(_ey){return E(_ex);})));},_ez=new T(function(){return B(unCStr("ETB"));}),_eA=23,_eB=function(_eC){var _eD=new T(function(){return B(A1(_eC,_eA));});return new T1(1,B(_c7(_ez,function(_eE){return E(_eD);})));},_eF=new T(function(){return B(unCStr("CAN"));}),_eG=24,_eH=function(_eI){var _eJ=new T(function(){return B(A1(_eI,_eG));});return new T1(1,B(_c7(_eF,function(_eK){return E(_eJ);})));},_eL=new T(function(){return B(unCStr("EM"));}),_eM=25,_eN=function(_eO){var _eP=new T(function(){return B(A1(_eO,_eM));});return new T1(1,B(_c7(_eL,function(_eQ){return E(_eP);})));},_eR=new T(function(){return B(unCStr("SUB"));}),_eS=26,_eT=function(_eU){var _eV=new T(function(){return B(A1(_eU,_eS));});return new T1(1,B(_c7(_eR,function(_eW){return E(_eV);})));},_eX=new T(function(){return B(unCStr("ESC"));}),_eY=27,_eZ=function(_f0){var _f1=new T(function(){return B(A1(_f0,_eY));});return new T1(1,B(_c7(_eX,function(_f2){return E(_f1);})));},_f3=new T(function(){return B(unCStr("FS"));}),_f4=28,_f5=function(_f6){var _f7=new T(function(){return B(A1(_f6,_f4));});return new T1(1,B(_c7(_f3,function(_f8){return E(_f7);})));},_f9=new T(function(){return B(unCStr("GS"));}),_fa=29,_fb=function(_fc){var _fd=new T(function(){return B(A1(_fc,_fa));});return new T1(1,B(_c7(_f9,function(_fe){return E(_fd);})));},_ff=new T(function(){return B(unCStr("RS"));}),_fg=30,_fh=function(_fi){var _fj=new T(function(){return B(A1(_fi,_fg));});return new T1(1,B(_c7(_ff,function(_fk){return E(_fj);})));},_fl=new T(function(){return B(unCStr("US"));}),_fm=31,_fn=function(_fo){var _fp=new T(function(){return B(A1(_fo,_fm));});return new T1(1,B(_c7(_fl,function(_fq){return E(_fp);})));},_fr=new T(function(){return B(unCStr("SP"));}),_fs=32,_ft=function(_fu){var _fv=new T(function(){return B(A1(_fu,_fs));});return new T1(1,B(_c7(_fr,function(_fw){return E(_fv);})));},_fx=new T(function(){return B(unCStr("DEL"));}),_fy=127,_fz=function(_fA){var _fB=new T(function(){return B(A1(_fA,_fy));});return new T1(1,B(_c7(_fx,function(_fC){return E(_fB);})));},_fD=new T2(1,_fz,_w),_fE=new T2(1,_ft,_fD),_fF=new T2(1,_fn,_fE),_fG=new T2(1,_fh,_fF),_fH=new T2(1,_fb,_fG),_fI=new T2(1,_f5,_fH),_fJ=new T2(1,_eZ,_fI),_fK=new T2(1,_eT,_fJ),_fL=new T2(1,_eN,_fK),_fM=new T2(1,_eH,_fL),_fN=new T2(1,_eB,_fM),_fO=new T2(1,_ev,_fN),_fP=new T2(1,_ep,_fO),_fQ=new T2(1,_ej,_fP),_fR=new T2(1,_ed,_fQ),_fS=new T2(1,_e7,_fR),_fT=new T2(1,_e1,_fS),_fU=new T2(1,_dV,_fT),_fV=new T2(1,_dP,_fU),_fW=new T2(1,_dJ,_fV),_fX=new T2(1,_dD,_fW),_fY=new T2(1,_dx,_fX),_fZ=new T2(1,_dr,_fY),_g0=new T2(1,_dl,_fZ),_g1=new T2(1,_df,_g0),_g2=new T2(1,_d9,_g1),_g3=new T2(1,_d3,_g2),_g4=new T2(1,_cX,_g3),_g5=new T2(1,_cR,_g4),_g6=new T2(1,_cL,_g5),_g7=new T2(1,_cF,_g6),_g8=new T2(1,_cz,_g7),_g9=new T2(1,_cv,_g8),_ga=new T(function(){return B(_bZ(_g9));}),_gb=34,_gc=new T1(0,1114111),_gd=92,_ge=39,_gf=function(_gg){var _gh=new T(function(){return B(A1(_gg,_d8));}),_gi=new T(function(){return B(A1(_gg,_de));}),_gj=new T(function(){return B(A1(_gg,_dk));}),_gk=new T(function(){return B(A1(_gg,_dq));}),_gl=new T(function(){return B(A1(_gg,_dw));}),_gm=new T(function(){return B(A1(_gg,_dC));}),_gn=new T(function(){return B(A1(_gg,_dI));}),_go=new T(function(){return B(A1(_gg,_gd));}),_gp=new T(function(){return B(A1(_gg,_ge));}),_gq=new T(function(){return B(A1(_gg,_gb));}),_gr=new T(function(){var _gs=function(_gt){var _gu=new T(function(){return B(_a6(E(_gt)));}),_gv=function(_gw){var _gx=B(_aH(_gu,_gw));if(!B(_bP(_gx,_gc))){return new T0(2);}else{return new F(function(){return A1(_gg,new T(function(){var _gy=B(_bM(_gx));if(_gy>>>0>1114111){return B(_bK(_gy));}else{return _gy;}}));});}};return new T1(1,B(_8I(_gt,_gv)));},_gz=new T(function(){var _gA=new T(function(){return B(A1(_gg,_fm));}),_gB=new T(function(){return B(A1(_gg,_fg));}),_gC=new T(function(){return B(A1(_gg,_fa));}),_gD=new T(function(){return B(A1(_gg,_f4));}),_gE=new T(function(){return B(A1(_gg,_eY));}),_gF=new T(function(){return B(A1(_gg,_eS));}),_gG=new T(function(){return B(A1(_gg,_eM));}),_gH=new T(function(){return B(A1(_gg,_eG));}),_gI=new T(function(){return B(A1(_gg,_eA));}),_gJ=new T(function(){return B(A1(_gg,_eu));}),_gK=new T(function(){return B(A1(_gg,_eo));}),_gL=new T(function(){return B(A1(_gg,_ei));}),_gM=new T(function(){return B(A1(_gg,_ec));}),_gN=new T(function(){return B(A1(_gg,_e6));}),_gO=new T(function(){return B(A1(_gg,_e0));}),_gP=new T(function(){return B(A1(_gg,_dU));}),_gQ=new T(function(){return B(A1(_gg,_dO));}),_gR=new T(function(){return B(A1(_gg,_ck));}),_gS=new T(function(){return B(A1(_gg,_d2));}),_gT=new T(function(){return B(A1(_gg,_cW));}),_gU=new T(function(){return B(A1(_gg,_cQ));}),_gV=new T(function(){return B(A1(_gg,_cK));}),_gW=new T(function(){return B(A1(_gg,_cE));}),_gX=new T(function(){return B(A1(_gg,_cq));}),_gY=new T(function(){return B(A1(_gg,_cy));}),_gZ=function(_h0){switch(E(_h0)){case 64:return E(_gY);case 65:return E(_gX);case 66:return E(_gW);case 67:return E(_gV);case 68:return E(_gU);case 69:return E(_gT);case 70:return E(_gS);case 71:return E(_gh);case 72:return E(_gi);case 73:return E(_gj);case 74:return E(_gk);case 75:return E(_gl);case 76:return E(_gm);case 77:return E(_gn);case 78:return E(_gR);case 79:return E(_gQ);case 80:return E(_gP);case 81:return E(_gO);case 82:return E(_gN);case 83:return E(_gM);case 84:return E(_gL);case 85:return E(_gK);case 86:return E(_gJ);case 87:return E(_gI);case 88:return E(_gH);case 89:return E(_gG);case 90:return E(_gF);case 91:return E(_gE);case 92:return E(_gD);case 93:return E(_gC);case 94:return E(_gB);case 95:return E(_gA);default:return new T0(2);}};return B(_6I(new T1(0,function(_h1){return (E(_h1)==94)?E(new T1(0,_gZ)):new T0(2);}),new T(function(){return B(A1(_ga,_gg));})));});return B(_6I(new T1(1,B(_81(_bv,_bx,_gs))),_gz));});return new F(function(){return _6I(new T1(0,function(_h2){switch(E(_h2)){case 34:return E(_gq);case 39:return E(_gp);case 92:return E(_go);case 97:return E(_gh);case 98:return E(_gi);case 102:return E(_gm);case 110:return E(_gk);case 114:return E(_gn);case 116:return E(_gj);case 118:return E(_gl);default:return new T0(2);}}),_gr);});},_h3=function(_h4){return new F(function(){return A1(_h4,_2v);});},_h5=function(_h6){var _h7=E(_h6);if(!_h7._){return E(_h3);}else{var _h8=E(_h7.a),_h9=_h8>>>0,_ha=new T(function(){return B(_h5(_h7.b));});if(_h9>887){var _hb=u_iswspace(_h8);if(!E(_hb)){return E(_h3);}else{var _hc=function(_hd){var _he=new T(function(){return B(A1(_ha,_hd));});return new T1(0,function(_hf){return E(_he);});};return E(_hc);}}else{var _hg=E(_h9);if(_hg==32){var _hh=function(_hi){var _hj=new T(function(){return B(A1(_ha,_hi));});return new T1(0,function(_hk){return E(_hj);});};return E(_hh);}else{if(_hg-9>>>0>4){if(E(_hg)==160){var _hl=function(_hm){var _hn=new T(function(){return B(A1(_ha,_hm));});return new T1(0,function(_ho){return E(_hn);});};return E(_hl);}else{return E(_h3);}}else{var _hp=function(_hq){var _hr=new T(function(){return B(A1(_ha,_hq));});return new T1(0,function(_hs){return E(_hr);});};return E(_hp);}}}}},_ht=function(_hu){var _hv=new T(function(){return B(_ht(_hu));}),_hw=function(_hx){return (E(_hx)==92)?E(_hv):new T0(2);},_hy=function(_hz){return E(new T1(0,_hw));},_hA=new T1(1,function(_hB){return new F(function(){return A2(_h5,_hB,_hy);});}),_hC=new T(function(){return B(_gf(function(_hD){return new F(function(){return A1(_hu,new T2(0,_hD,_bp));});}));}),_hE=function(_hF){var _hG=E(_hF);if(_hG==38){return E(_hv);}else{var _hH=_hG>>>0;if(_hH>887){var _hI=u_iswspace(_hG);return (E(_hI)==0)?new T0(2):E(_hA);}else{var _hJ=E(_hH);return (_hJ==32)?E(_hA):(_hJ-9>>>0>4)?(E(_hJ)==160)?E(_hA):new T0(2):E(_hA);}}};return new F(function(){return _6I(new T1(0,function(_hK){return (E(_hK)==92)?E(new T1(0,_hE)):new T0(2);}),new T1(0,function(_hL){var _hM=E(_hL);if(E(_hM)==92){return E(_hC);}else{return new F(function(){return A1(_hu,new T2(0,_hM,_bo));});}}));});},_hN=function(_hO,_hP){var _hQ=new T(function(){return B(A1(_hP,new T1(1,new T(function(){return B(A1(_hO,_w));}))));}),_hR=function(_hS){var _hT=E(_hS),_hU=E(_hT.a);if(E(_hU)==34){if(!E(_hT.b)){return E(_hQ);}else{return new F(function(){return _hN(function(_hV){return new F(function(){return A1(_hO,new T2(1,_hU,_hV));});},_hP);});}}else{return new F(function(){return _hN(function(_hW){return new F(function(){return A1(_hO,new T2(1,_hU,_hW));});},_hP);});}};return new F(function(){return _ht(_hR);});},_hX=new T(function(){return B(unCStr("_\'"));}),_hY=function(_hZ){var _i0=u_iswalnum(_hZ);if(!E(_i0)){return new F(function(){return _bg(_7x,_hZ,_hX);});}else{return true;}},_i1=function(_i2){return new F(function(){return _hY(E(_i2));});},_i3=new T(function(){return B(unCStr(",;()[]{}`"));}),_i4=new T(function(){return B(unCStr("=>"));}),_i5=new T2(1,_i4,_w),_i6=new T(function(){return B(unCStr("~"));}),_i7=new T2(1,_i6,_i5),_i8=new T(function(){return B(unCStr("@"));}),_i9=new T2(1,_i8,_i7),_ia=new T(function(){return B(unCStr("->"));}),_ib=new T2(1,_ia,_i9),_ic=new T(function(){return B(unCStr("<-"));}),_id=new T2(1,_ic,_ib),_ie=new T(function(){return B(unCStr("|"));}),_if=new T2(1,_ie,_id),_ig=new T(function(){return B(unCStr("\\"));}),_ih=new T2(1,_ig,_if),_ii=new T(function(){return B(unCStr("="));}),_ij=new T2(1,_ii,_ih),_ik=new T(function(){return B(unCStr("::"));}),_il=new T2(1,_ik,_ij),_im=new T(function(){return B(unCStr(".."));}),_in=new T2(1,_im,_il),_io=function(_ip){var _iq=new T(function(){return B(A1(_ip,_8F));}),_ir=new T(function(){var _is=new T(function(){var _it=function(_iu){var _iv=new T(function(){return B(A1(_ip,new T1(0,_iu)));});return new T1(0,function(_iw){return (E(_iw)==39)?E(_iv):new T0(2);});};return B(_gf(_it));}),_ix=function(_iy){var _iz=E(_iy);switch(E(_iz)){case 39:return new T0(2);case 92:return E(_is);default:var _iA=new T(function(){return B(A1(_ip,new T1(0,_iz)));});return new T1(0,function(_iB){return (E(_iB)==39)?E(_iA):new T0(2);});}},_iC=new T(function(){var _iD=new T(function(){return B(_hN(_2s,_ip));}),_iE=new T(function(){var _iF=new T(function(){var _iG=new T(function(){var _iH=function(_iI){var _iJ=E(_iI),_iK=u_iswalpha(_iJ);return (E(_iK)==0)?(E(_iJ)==95)?new T1(1,B(_8r(_i1,function(_iL){return new F(function(){return A1(_ip,new T1(3,new T2(1,_iJ,_iL)));});}))):new T0(2):new T1(1,B(_8r(_i1,function(_iM){return new F(function(){return A1(_ip,new T1(3,new T2(1,_iJ,_iM)));});})));};return B(_6I(new T1(0,_iH),new T(function(){return new T1(1,B(_81(_9D,_be,_ip)));})));}),_iN=function(_iO){return (!B(_bg(_7x,_iO,_bl)))?new T0(2):new T1(1,B(_8r(_bm,function(_iP){var _iQ=new T2(1,_iO,_iP);if(!B(_bg(_7G,_iQ,_in))){return new F(function(){return A1(_ip,new T1(4,_iQ));});}else{return new F(function(){return A1(_ip,new T1(2,_iQ));});}})));};return B(_6I(new T1(0,_iN),_iG));});return B(_6I(new T1(0,function(_iR){if(!B(_bg(_7x,_iR,_i3))){return new T0(2);}else{return new F(function(){return A1(_ip,new T1(2,new T2(1,_iR,_w)));});}}),_iF));});return B(_6I(new T1(0,function(_iS){return (E(_iS)==34)?E(_iD):new T0(2);}),_iE));});return B(_6I(new T1(0,function(_iT){return (E(_iT)==39)?E(new T1(0,_ix)):new T0(2);}),_iC));});return new F(function(){return _6I(new T1(1,function(_iU){return (E(_iU)._==0)?E(_iq):new T0(2);}),_ir);});},_iV=0,_iW=function(_iX,_iY){var _iZ=new T(function(){var _j0=new T(function(){var _j1=function(_j2){var _j3=new T(function(){var _j4=new T(function(){return B(A1(_iY,_j2));});return B(_io(function(_j5){var _j6=E(_j5);return (_j6._==2)?(!B(_7m(_j6.a,_7l)))?new T0(2):E(_j4):new T0(2);}));}),_j7=function(_j8){return E(_j3);};return new T1(1,function(_j9){return new F(function(){return A2(_h5,_j9,_j7);});});};return B(A2(_iX,_iV,_j1));});return B(_io(function(_ja){var _jb=E(_ja);return (_jb._==2)?(!B(_7m(_jb.a,_7k)))?new T0(2):E(_j0):new T0(2);}));}),_jc=function(_jd){return E(_iZ);};return function(_je){return new F(function(){return A2(_h5,_je,_jc);});};},_jf=function(_jg,_jh){var _ji=function(_jj){var _jk=new T(function(){return B(A1(_jg,_jj));}),_jl=function(_jm){return new F(function(){return _6I(B(A1(_jk,_jm)),new T(function(){return new T1(1,B(_iW(_ji,_jm)));}));});};return E(_jl);},_jn=new T(function(){return B(A1(_jg,_jh));}),_jo=function(_jp){return new F(function(){return _6I(B(A1(_jn,_jp)),new T(function(){return new T1(1,B(_iW(_ji,_jp)));}));});};return E(_jo);},_jq=function(_jr,_js){var _jt=function(_ju,_jv){var _jw=function(_jx){return new F(function(){return A1(_jv,new T(function(){return  -E(_jx);}));});},_jy=new T(function(){return B(_io(function(_jz){return new F(function(){return A3(_jr,_jz,_ju,_jw);});}));}),_jA=function(_jB){return E(_jy);},_jC=function(_jD){return new F(function(){return A2(_h5,_jD,_jA);});},_jE=new T(function(){return B(_io(function(_jF){var _jG=E(_jF);if(_jG._==4){var _jH=E(_jG.a);if(!_jH._){return new F(function(){return A3(_jr,_jG,_ju,_jv);});}else{if(E(_jH.a)==45){if(!E(_jH.b)._){return E(new T1(1,_jC));}else{return new F(function(){return A3(_jr,_jG,_ju,_jv);});}}else{return new F(function(){return A3(_jr,_jG,_ju,_jv);});}}}else{return new F(function(){return A3(_jr,_jG,_ju,_jv);});}}));}),_jI=function(_jJ){return E(_jE);};return new T1(1,function(_jK){return new F(function(){return A2(_h5,_jK,_jI);});});};return new F(function(){return _jf(_jt,_js);});},_jL=new T(function(){return 1/0;}),_jM=function(_jN,_jO){return new F(function(){return A1(_jO,_jL);});},_jP=new T(function(){return 0/0;}),_jQ=function(_jR,_jS){return new F(function(){return A1(_jS,_jP);});},_jT=new T(function(){return B(unCStr("NaN"));}),_jU=new T(function(){return B(unCStr("Infinity"));}),_jV=1024,_jW=-1021,_jX=new T(function(){return B(unCStr("base"));}),_jY=new T(function(){return B(unCStr("GHC.Exception"));}),_jZ=new T(function(){return B(unCStr("ArithException"));}),_k0=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_jX,_jY,_jZ),_k1=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_k0,_w,_w),_k2=function(_k3){return E(_k1);},_k4=function(_k5){var _k6=E(_k5);return new F(function(){return _C(B(_A(_k6.a)),_k2,_k6.b);});},_k7=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_k8=new T(function(){return B(unCStr("denormal"));}),_k9=new T(function(){return B(unCStr("divide by zero"));}),_ka=new T(function(){return B(unCStr("loss of precision"));}),_kb=new T(function(){return B(unCStr("arithmetic underflow"));}),_kc=new T(function(){return B(unCStr("arithmetic overflow"));}),_kd=function(_ke,_kf){switch(E(_ke)){case 0:return new F(function(){return _Q(_kc,_kf);});break;case 1:return new F(function(){return _Q(_kb,_kf);});break;case 2:return new F(function(){return _Q(_ka,_kf);});break;case 3:return new F(function(){return _Q(_k9,_kf);});break;case 4:return new F(function(){return _Q(_k8,_kf);});break;default:return new F(function(){return _Q(_k7,_kf);});}},_kg=function(_kh){return new F(function(){return _kd(_kh,_w);});},_ki=function(_kj,_kk,_kl){return new F(function(){return _kd(_kk,_kl);});},_km=function(_kn,_ko){return new F(function(){return _1U(_kd,_kn,_ko);});},_kp=new T3(0,_ki,_kg,_km),_kq=new T(function(){return new T5(0,_k2,_kp,_kr,_k4,_kg);}),_kr=function(_68){return new T2(0,_kq,_68);},_ks=3,_kt=new T(function(){return B(_kr(_ks));}),_ku=new T(function(){return die(_kt);}),_kv=function(_kw,_kx){var _ky=E(_kw);if(!_ky._){var _kz=_ky.a,_kA=E(_kx);return (_kA._==0)?_kz==_kA.a:(I_compareInt(_kA.a,_kz)==0)?true:false;}else{var _kB=_ky.a,_kC=E(_kx);return (_kC._==0)?(I_compareInt(_kB,_kC.a)==0)?true:false:(I_compare(_kB,_kC.a)==0)?true:false;}},_kD=new T1(0,0),_kE=function(_kF,_kG){while(1){var _kH=E(_kF);if(!_kH._){var _kI=E(_kH.a);if(_kI==(-2147483648)){_kF=new T1(1,I_fromInt(-2147483648));continue;}else{var _kJ=E(_kG);if(!_kJ._){return new T1(0,_kI%_kJ.a);}else{_kF=new T1(1,I_fromInt(_kI));_kG=_kJ;continue;}}}else{var _kK=_kH.a,_kL=E(_kG);return (_kL._==0)?new T1(1,I_rem(_kK,I_fromInt(_kL.a))):new T1(1,I_rem(_kK,_kL.a));}}},_kM=function(_kN,_kO){if(!B(_kv(_kO,_kD))){return new F(function(){return _kE(_kN,_kO);});}else{return E(_ku);}},_kP=function(_kQ,_kR){while(1){if(!B(_kv(_kR,_kD))){var _kS=_kR,_kT=B(_kM(_kQ,_kR));_kQ=_kS;_kR=_kT;continue;}else{return E(_kQ);}}},_kU=function(_kV){var _kW=E(_kV);if(!_kW._){var _kX=E(_kW.a);return (_kX==(-2147483648))?E(_9V):(_kX<0)?new T1(0, -_kX):E(_kW);}else{var _kY=_kW.a;return (I_compareInt(_kY,0)>=0)?E(_kW):new T1(1,I_negate(_kY));}},_kZ=function(_l0,_l1){while(1){var _l2=E(_l0);if(!_l2._){var _l3=E(_l2.a);if(_l3==(-2147483648)){_l0=new T1(1,I_fromInt(-2147483648));continue;}else{var _l4=E(_l1);if(!_l4._){return new T1(0,quot(_l3,_l4.a));}else{_l0=new T1(1,I_fromInt(_l3));_l1=_l4;continue;}}}else{var _l5=_l2.a,_l6=E(_l1);return (_l6._==0)?new T1(0,I_toInt(I_quot(_l5,I_fromInt(_l6.a)))):new T1(1,I_quot(_l5,_l6.a));}}},_l7=5,_l8=new T(function(){return B(_kr(_l7));}),_l9=new T(function(){return die(_l8);}),_la=function(_lb,_lc){if(!B(_kv(_lc,_kD))){var _ld=B(_kP(B(_kU(_lb)),B(_kU(_lc))));return (!B(_kv(_ld,_kD)))?new T2(0,B(_kZ(_lb,_ld)),B(_kZ(_lc,_ld))):E(_ku);}else{return E(_l9);}},_le=new T1(0,1),_lf=new T(function(){return B(unCStr("Negative exponent"));}),_lg=new T(function(){return B(err(_lf));}),_lh=new T1(0,2),_li=new T(function(){return B(_kv(_lh,_kD));}),_lj=function(_lk,_ll){while(1){var _lm=E(_lk);if(!_lm._){var _ln=_lm.a,_lo=E(_ll);if(!_lo._){var _lp=_lo.a,_lq=subC(_ln,_lp);if(!E(_lq.b)){return new T1(0,_lq.a);}else{_lk=new T1(1,I_fromInt(_ln));_ll=new T1(1,I_fromInt(_lp));continue;}}else{_lk=new T1(1,I_fromInt(_ln));_ll=_lo;continue;}}else{var _lr=E(_ll);if(!_lr._){_lk=_lm;_ll=new T1(1,I_fromInt(_lr.a));continue;}else{return new T1(1,I_sub(_lm.a,_lr.a));}}}},_ls=function(_lt,_lu,_lv){while(1){if(!E(_li)){if(!B(_kv(B(_kE(_lu,_lh)),_kD))){if(!B(_kv(_lu,_le))){var _lw=B(_ac(_lt,_lt)),_lx=B(_kZ(B(_lj(_lu,_le)),_lh)),_ly=B(_ac(_lt,_lv));_lt=_lw;_lu=_lx;_lv=_ly;continue;}else{return new F(function(){return _ac(_lt,_lv);});}}else{var _lw=B(_ac(_lt,_lt)),_lx=B(_kZ(_lu,_lh));_lt=_lw;_lu=_lx;continue;}}else{return E(_ku);}}},_lz=function(_lA,_lB){while(1){if(!E(_li)){if(!B(_kv(B(_kE(_lB,_lh)),_kD))){if(!B(_kv(_lB,_le))){return new F(function(){return _ls(B(_ac(_lA,_lA)),B(_kZ(B(_lj(_lB,_le)),_lh)),_lA);});}else{return E(_lA);}}else{var _lC=B(_ac(_lA,_lA)),_lD=B(_kZ(_lB,_lh));_lA=_lC;_lB=_lD;continue;}}else{return E(_ku);}}},_lE=function(_lF,_lG){var _lH=E(_lF);if(!_lH._){var _lI=_lH.a,_lJ=E(_lG);return (_lJ._==0)?_lI<_lJ.a:I_compareInt(_lJ.a,_lI)>0;}else{var _lK=_lH.a,_lL=E(_lG);return (_lL._==0)?I_compareInt(_lK,_lL.a)<0:I_compare(_lK,_lL.a)<0;}},_lM=function(_lN,_lO){if(!B(_lE(_lO,_kD))){if(!B(_kv(_lO,_kD))){return new F(function(){return _lz(_lN,_lO);});}else{return E(_le);}}else{return E(_lg);}},_lP=new T1(0,1),_lQ=new T1(0,0),_lR=new T1(0,-1),_lS=function(_lT){var _lU=E(_lT);if(!_lU._){var _lV=_lU.a;return (_lV>=0)?(E(_lV)==0)?E(_lQ):E(_9K):E(_lR);}else{var _lW=I_compareInt(_lU.a,0);return (_lW<=0)?(E(_lW)==0)?E(_lQ):E(_lR):E(_9K);}},_lX=function(_lY,_lZ,_m0){while(1){var _m1=E(_m0);if(!_m1._){if(!B(_lE(_lY,_ap))){return new T2(0,B(_ac(_lZ,B(_lM(_a0,_lY)))),_le);}else{var _m2=B(_lM(_a0,B(_9W(_lY))));return new F(function(){return _la(B(_ac(_lZ,B(_lS(_m2)))),B(_kU(_m2)));});}}else{var _m3=B(_lj(_lY,_lP)),_m4=B(_9M(B(_ac(_lZ,_a0)),B(_a6(E(_m1.a)))));_lY=_m3;_lZ=_m4;_m0=_m1.b;continue;}}},_m5=function(_m6,_m7){var _m8=E(_m6);if(!_m8._){var _m9=_m8.a,_ma=E(_m7);return (_ma._==0)?_m9>=_ma.a:I_compareInt(_ma.a,_m9)<=0;}else{var _mb=_m8.a,_mc=E(_m7);return (_mc._==0)?I_compareInt(_mb,_mc.a)>=0:I_compare(_mb,_mc.a)>=0;}},_md=function(_me){var _mf=E(_me);if(!_mf._){var _mg=_mf.b;return new F(function(){return _la(B(_ac(B(_aq(new T(function(){return B(_a6(E(_mf.a)));}),new T(function(){return B(_a1(_mg,0));},1),B(_4J(_a8,_mg)))),_lP)),_lP);});}else{var _mh=_mf.a,_mi=_mf.c,_mj=E(_mf.b);if(!_mj._){var _mk=E(_mi);if(!_mk._){return new F(function(){return _la(B(_ac(B(_aH(_a0,_mh)),_lP)),_lP);});}else{var _ml=_mk.a;if(!B(_m5(_ml,_ap))){var _mm=B(_lM(_a0,B(_9W(_ml))));return new F(function(){return _la(B(_ac(B(_aH(_a0,_mh)),B(_lS(_mm)))),B(_kU(_mm)));});}else{return new F(function(){return _la(B(_ac(B(_ac(B(_aH(_a0,_mh)),B(_lM(_a0,_ml)))),_lP)),_lP);});}}}else{var _mn=_mj.a,_mo=E(_mi);if(!_mo._){return new F(function(){return _lX(_ap,B(_aH(_a0,_mh)),_mn);});}else{return new F(function(){return _lX(_mo.a,B(_aH(_a0,_mh)),_mn);});}}}},_mp=function(_mq,_mr){while(1){var _ms=E(_mr);if(!_ms._){return __Z;}else{if(!B(A1(_mq,_ms.a))){return E(_ms);}else{_mr=_ms.b;continue;}}}},_mt=function(_mu,_mv){var _mw=E(_mu);if(!_mw._){var _mx=_mw.a,_my=E(_mv);return (_my._==0)?_mx>_my.a:I_compareInt(_my.a,_mx)<0;}else{var _mz=_mw.a,_mA=E(_mv);return (_mA._==0)?I_compareInt(_mz,_mA.a)>0:I_compare(_mz,_mA.a)>0;}},_mB=0,_mC=function(_mD,_mE){return E(_mD)==E(_mE);},_mF=function(_mG){return new F(function(){return _mC(_mB,_mG);});},_mH=new T2(0,E(_ap),E(_le)),_mI=new T1(1,_mH),_mJ=new T1(0,-2147483648),_mK=new T1(0,2147483647),_mL=function(_mM,_mN,_mO){var _mP=E(_mO);if(!_mP._){return new T1(1,new T(function(){var _mQ=B(_md(_mP));return new T2(0,E(_mQ.a),E(_mQ.b));}));}else{var _mR=E(_mP.c);if(!_mR._){return new T1(1,new T(function(){var _mS=B(_md(_mP));return new T2(0,E(_mS.a),E(_mS.b));}));}else{var _mT=_mR.a;if(!B(_mt(_mT,_mK))){if(!B(_lE(_mT,_mJ))){var _mU=function(_mV){var _mW=_mV+B(_bM(_mT))|0;return (_mW<=(E(_mN)+3|0))?(_mW>=(E(_mM)-3|0))?new T1(1,new T(function(){var _mX=B(_md(_mP));return new T2(0,E(_mX.a),E(_mX.b));})):E(_mI):__Z;},_mY=B(_mp(_mF,_mP.a));if(!_mY._){var _mZ=E(_mP.b);if(!_mZ._){return E(_mI);}else{var _n0=B(_69(_mF,_mZ.a));if(!E(_n0.b)._){return E(_mI);}else{return new F(function(){return _mU( -B(_a1(_n0.a,0)));});}}}else{return new F(function(){return _mU(B(_a1(_mY,0)));});}}else{return __Z;}}else{return __Z;}}}},_n1=function(_n2,_n3){return new T0(2);},_n4=new T1(0,1),_n5=function(_n6,_n7){var _n8=E(_n6);if(!_n8._){var _n9=_n8.a,_na=E(_n7);if(!_na._){var _nb=_na.a;return (_n9!=_nb)?(_n9>_nb)?2:0:1;}else{var _nc=I_compareInt(_na.a,_n9);return (_nc<=0)?(_nc>=0)?1:2:0;}}else{var _nd=_n8.a,_ne=E(_n7);if(!_ne._){var _nf=I_compareInt(_nd,_ne.a);return (_nf>=0)?(_nf<=0)?1:2:0;}else{var _ng=I_compare(_nd,_ne.a);return (_ng>=0)?(_ng<=0)?1:2:0;}}},_nh=function(_ni,_nj){var _nk=E(_ni);return (_nk._==0)?_nk.a*Math.pow(2,_nj):I_toNumber(_nk.a)*Math.pow(2,_nj);},_nl=function(_nm,_nn){while(1){var _no=E(_nm);if(!_no._){var _np=E(_no.a);if(_np==(-2147483648)){_nm=new T1(1,I_fromInt(-2147483648));continue;}else{var _nq=E(_nn);if(!_nq._){var _nr=_nq.a;return new T2(0,new T1(0,quot(_np,_nr)),new T1(0,_np%_nr));}else{_nm=new T1(1,I_fromInt(_np));_nn=_nq;continue;}}}else{var _ns=E(_nn);if(!_ns._){_nm=_no;_nn=new T1(1,I_fromInt(_ns.a));continue;}else{var _nt=I_quotRem(_no.a,_ns.a);return new T2(0,new T1(1,_nt.a),new T1(1,_nt.b));}}}},_nu=new T1(0,0),_nv=function(_nw,_nx){while(1){var _ny=E(_nw);if(!_ny._){_nw=new T1(1,I_fromInt(_ny.a));continue;}else{return new T1(1,I_shiftLeft(_ny.a,_nx));}}},_nz=function(_nA,_nB,_nC){if(!B(_kv(_nC,_nu))){var _nD=B(_nl(_nB,_nC)),_nE=_nD.a;switch(B(_n5(B(_nv(_nD.b,1)),_nC))){case 0:return new F(function(){return _nh(_nE,_nA);});break;case 1:if(!(B(_bM(_nE))&1)){return new F(function(){return _nh(_nE,_nA);});}else{return new F(function(){return _nh(B(_9M(_nE,_n4)),_nA);});}break;default:return new F(function(){return _nh(B(_9M(_nE,_n4)),_nA);});}}else{return E(_ku);}},_nF=function(_nG){var _nH=function(_nI,_nJ){while(1){if(!B(_lE(_nI,_nG))){if(!B(_mt(_nI,_nG))){if(!B(_kv(_nI,_nG))){return new F(function(){return _6v("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_nJ);}}else{return _nJ-1|0;}}else{var _nK=B(_nv(_nI,1)),_nL=_nJ+1|0;_nI=_nK;_nJ=_nL;continue;}}};return new F(function(){return _nH(_9K,0);});},_nM=function(_nN){var _nO=E(_nN);if(!_nO._){var _nP=_nO.a>>>0;if(!_nP){return -1;}else{var _nQ=function(_nR,_nS){while(1){if(_nR>=_nP){if(_nR<=_nP){if(_nR!=_nP){return new F(function(){return _6v("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_nS);}}else{return _nS-1|0;}}else{var _nT=imul(_nR,2)>>>0,_nU=_nS+1|0;_nR=_nT;_nS=_nU;continue;}}};return new F(function(){return _nQ(1,0);});}}else{return new F(function(){return _nF(_nO);});}},_nV=function(_nW){var _nX=E(_nW);if(!_nX._){var _nY=_nX.a>>>0;if(!_nY){return new T2(0,-1,0);}else{var _nZ=function(_o0,_o1){while(1){if(_o0>=_nY){if(_o0<=_nY){if(_o0!=_nY){return new F(function(){return _6v("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_o1);}}else{return _o1-1|0;}}else{var _o2=imul(_o0,2)>>>0,_o3=_o1+1|0;_o0=_o2;_o1=_o3;continue;}}};return new T2(0,B(_nZ(1,0)),(_nY&_nY-1>>>0)>>>0&4294967295);}}else{var _o4=_nX.a;return new T2(0,B(_nM(_nX)),I_compareInt(I_and(_o4,I_sub(_o4,I_fromInt(1))),0));}},_o5=function(_o6,_o7){while(1){var _o8=E(_o6);if(!_o8._){var _o9=_o8.a,_oa=E(_o7);if(!_oa._){return new T1(0,(_o9>>>0&_oa.a>>>0)>>>0&4294967295);}else{_o6=new T1(1,I_fromInt(_o9));_o7=_oa;continue;}}else{var _ob=E(_o7);if(!_ob._){_o6=_o8;_o7=new T1(1,I_fromInt(_ob.a));continue;}else{return new T1(1,I_and(_o8.a,_ob.a));}}}},_oc=new T1(0,2),_od=function(_oe,_of){var _og=E(_oe);if(!_og._){var _oh=(_og.a>>>0&(2<<_of>>>0)-1>>>0)>>>0,_oi=1<<_of>>>0;return (_oi<=_oh)?(_oi>=_oh)?1:2:0;}else{var _oj=B(_o5(_og,B(_lj(B(_nv(_oc,_of)),_9K)))),_ok=B(_nv(_9K,_of));return (!B(_mt(_ok,_oj)))?(!B(_lE(_ok,_oj)))?1:2:0;}},_ol=function(_om,_on){while(1){var _oo=E(_om);if(!_oo._){_om=new T1(1,I_fromInt(_oo.a));continue;}else{return new T1(1,I_shiftRight(_oo.a,_on));}}},_op=function(_oq,_or,_os,_ot){var _ou=B(_nV(_ot)),_ov=_ou.a;if(!E(_ou.b)){var _ow=B(_nM(_os));if(_ow<((_ov+_oq|0)-1|0)){var _ox=_ov+(_oq-_or|0)|0;if(_ox>0){if(_ox>_ow){if(_ox<=(_ow+1|0)){if(!E(B(_nV(_os)).b)){return 0;}else{return new F(function(){return _nh(_n4,_oq-_or|0);});}}else{return 0;}}else{var _oy=B(_ol(_os,_ox));switch(B(_od(_os,_ox-1|0))){case 0:return new F(function(){return _nh(_oy,_oq-_or|0);});break;case 1:if(!(B(_bM(_oy))&1)){return new F(function(){return _nh(_oy,_oq-_or|0);});}else{return new F(function(){return _nh(B(_9M(_oy,_n4)),_oq-_or|0);});}break;default:return new F(function(){return _nh(B(_9M(_oy,_n4)),_oq-_or|0);});}}}else{return new F(function(){return _nh(_os,(_oq-_or|0)-_ox|0);});}}else{if(_ow>=_or){var _oz=B(_ol(_os,(_ow+1|0)-_or|0));switch(B(_od(_os,_ow-_or|0))){case 0:return new F(function(){return _nh(_oz,((_ow-_ov|0)+1|0)-_or|0);});break;case 2:return new F(function(){return _nh(B(_9M(_oz,_n4)),((_ow-_ov|0)+1|0)-_or|0);});break;default:if(!(B(_bM(_oz))&1)){return new F(function(){return _nh(_oz,((_ow-_ov|0)+1|0)-_or|0);});}else{return new F(function(){return _nh(B(_9M(_oz,_n4)),((_ow-_ov|0)+1|0)-_or|0);});}}}else{return new F(function(){return _nh(_os, -_ov);});}}}else{var _oA=B(_nM(_os))-_ov|0,_oB=function(_oC){var _oD=function(_oE,_oF){if(!B(_bP(B(_nv(_oF,_or)),_oE))){return new F(function(){return _nz(_oC-_or|0,_oE,_oF);});}else{return new F(function(){return _nz((_oC-_or|0)+1|0,_oE,B(_nv(_oF,1)));});}};if(_oC>=_or){if(_oC!=_or){return new F(function(){return _oD(_os,new T(function(){return B(_nv(_ot,_oC-_or|0));}));});}else{return new F(function(){return _oD(_os,_ot);});}}else{return new F(function(){return _oD(new T(function(){return B(_nv(_os,_or-_oC|0));}),_ot);});}};if(_oq>_oA){return new F(function(){return _oB(_oq);});}else{return new F(function(){return _oB(_oA);});}}},_oG=new T(function(){return 0/0;}),_oH=new T(function(){return -1/0;}),_oI=new T(function(){return 1/0;}),_oJ=0,_oK=function(_oL,_oM){if(!B(_kv(_oM,_nu))){if(!B(_kv(_oL,_nu))){if(!B(_lE(_oL,_nu))){return new F(function(){return _op(-1021,53,_oL,_oM);});}else{return  -B(_op(-1021,53,B(_9W(_oL)),_oM));}}else{return E(_oJ);}}else{return (!B(_kv(_oL,_nu)))?(!B(_lE(_oL,_nu)))?E(_oI):E(_oH):E(_oG);}},_oN=function(_oO){var _oP=E(_oO);switch(_oP._){case 3:var _oQ=_oP.a;return (!B(_7m(_oQ,_jU)))?(!B(_7m(_oQ,_jT)))?E(_n1):E(_jQ):E(_jM);case 5:var _oR=B(_mL(_jW,_jV,_oP.a));if(!_oR._){return E(_jM);}else{var _oS=new T(function(){var _oT=E(_oR.a);return B(_oK(_oT.a,_oT.b));});return function(_oU,_oV){return new F(function(){return A1(_oV,_oS);});};}break;default:return E(_n1);}},_oW=function(_oX){var _oY=function(_oZ){return E(new T2(3,_oX,_7S));};return new T1(1,function(_p0){return new F(function(){return A2(_h5,_p0,_oY);});});},_p1=new T(function(){return B(A3(_jq,_oN,_iV,_oW));}),_p2=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_p3=function(_p4){return new F(function(){return _66(new T1(0,new T(function(){return B(_6k(_p4,_p2));})),_5Q);});},_p5=new T(function(){return B(_p3("SMHI.hs:26:5-38|Str json"));}),_p6="value",_p7=function(_p8){while(1){var _p9=B((function(_pa){var _pb=E(_pa);if(!_pb._){return __Z;}else{var _pc=_pb.b,_pd=E(_pb.a);if(!E(_pd.b)._){return new T2(1,_pd.a,new T(function(){return B(_p7(_pc));}));}else{_p8=_pc;return __continue;}}})(_p8));if(_p9!=__continue){return _p9;}}},_pe=function(_pf,_pg){var _ph=E(_pg);if(!_ph._){return __Z;}else{var _pi=new T(function(){return B(_pe(new T(function(){return E(_pf)+1;}),_ph.b));}),_pj=new T(function(){var _pk=B(_p7(B(_6y(_p1,new T(function(){var _pl=B(_39(_ph.a,_p6));if(_pl._==1){return fromJSStr(_pl.a);}else{return E(_p5);}})))));if(!_pk._){return E(_5z);}else{if(!E(_pk.b)._){return E(_pk.a);}else{return E(_5B);}}});return new T2(1,new T2(0,_pf,_pj),_pi);}},_pm=new T(function(){return B(unCStr("http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/71420/period/latest-months/data.json"));}),_pn=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_po=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_pp=function(_pq,_pr,_){var _ps=E(_pq);if(!_ps._){return _2v;}else{var _pt=E(_ps.a),_pu=E(_pr),_pv=__app3(E(_pn),_pu,E(_pt.a),E(_pt.b)),_pw=E(_ps.b);if(!_pw._){return _2v;}else{var _px=E(_pw.a),_py=E(_po),_pz=__app3(_py,_pu,E(_px.a),E(_px.b)),_pA=function(_pB,_){while(1){var _pC=E(_pB);if(!_pC._){return _2v;}else{var _pD=E(_pC.a),_pE=__app3(_py,_pu,E(_pD.a),E(_pD.b));_pB=_pC.b;continue;}}};return new F(function(){return _pA(_pw.b,_);});}}},_pF=50,_pG=800,_pH=new T2(0,_pG,_pF),_pI=new T2(1,_pH,_w),_pJ=0,_pK=new T2(0,_pJ,_pF),_pL=new T2(1,_pK,_pI),_pM=100,_pN=new T2(0,_pG,_pM),_pO=new T2(1,_pN,_w),_pP=new T2(0,_pJ,_pM),_pQ=new T2(1,_pP,_pO),_pR=150,_pS=new T2(0,_pG,_pR),_pT=new T2(1,_pS,_w),_pU=new T2(0,_pJ,_pR),_pV=new T2(1,_pU,_pT),_pW=200,_pX=new T2(0,_pG,_pW),_pY=new T2(1,_pX,_w),_pZ=new T2(0,_pJ,_pW),_q0=new T2(1,_pZ,_pY),_q1=250,_q2=new T2(0,_pG,_q1),_q3=new T2(1,_q2,_w),_q4=new T2(0,_pJ,_q1),_q5=new T2(1,_q4,_q3),_q6=function(_q7,_){var _q8=B(_pp(_q5,_q7,_)),_q9=B(_pp(_q0,_q7,_)),_qa=B(_pp(_pV,_q7,_)),_qb=B(_pp(_pQ,_q7,_));return new F(function(){return _pp(_pL,_q7,_);});},_qc=new T(function(){return B(_p3("SMHI.hs:40:15-60|Arr dataPoints"));}),_qd=300,_qe=function(_qf,_qg,_){while(1){var _qh=B((function(_qi,_qj,_){var _qk=E(_qi);if(!_qk._){return _2v;}else{var _ql=E(_qk.a),_qm=_ql.a,_qn=new T(function(){return E(_qm)+1;}),_qo=new T(function(){return 200-E(_ql.b)*5;}),_qp=B(_pp(new T2(1,new T2(0,_qm,_qd),new T2(1,new T2(0,_qn,_qd),new T2(1,new T2(0,_qn,_qo),new T2(1,new T2(0,_qm,_qo),new T2(1,new T2(0,_qm,_qd),_w))))),_qj,_)),_qq=_qj;_qf=_qk.b;_qg=_qq;return __continue;}})(_qf,_qg,_));if(_qh!=__continue){return _qh;}}},_qr=new T3(0,128,128,128),_qs=",",_qt="rgba(",_qu=new T(function(){return toJSStr(_w);}),_qv="rgb(",_qw=")",_qx=new T2(1,_qw,_w),_qy=function(_qz){var _qA=E(_qz);if(!_qA._){var _qB=jsCat(new T2(1,_qv,new T2(1,new T(function(){return String(_qA.a);}),new T2(1,_qs,new T2(1,new T(function(){return String(_qA.b);}),new T2(1,_qs,new T2(1,new T(function(){return String(_qA.c);}),_qx)))))),E(_qu));return E(_qB);}else{var _qC=jsCat(new T2(1,_qt,new T2(1,new T(function(){return String(_qA.a);}),new T2(1,_qs,new T2(1,new T(function(){return String(_qA.b);}),new T2(1,_qs,new T2(1,new T(function(){return String(_qA.c);}),new T2(1,_qs,new T2(1,new T(function(){return String(_qA.d);}),_qx)))))))),E(_qu));return E(_qC);}},_qD="fillStyle",_qE=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_qF=function(_qG){var _qH=new T(function(){return B(_qy(_qG));});return function(_qI,_){var _qJ=__app3(E(_qE),E(_qI),E(_qD),E(_qH));return new F(function(){return _49(_);});};},_qK=new T(function(){return B(_qF(_qr));}),_qL=new T(function(){return eval("(function(x){console.log(x);})");}),_qM=function(_qN,_qO){var _qP=function(_){var _qQ=__app1(E(_qL),toJSStr(E(_qO)));return new F(function(){return _49(_);});};return new F(function(){return A2(_2D,_qN,_qP);});},_qR=new T(function(){return B(_qM(_2u,_pm));}),_qS=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_qT=function(_qU,_qV,_qW){var _qX=new T(function(){return toJSStr(E(_qW));});return function(_qY,_){var _qZ=__app4(E(_qS),E(_qY),E(_qX),E(_qU),E(_qV));return new F(function(){return _49(_);});};},_r0=new T(function(){return B(unCStr("30\u00b0 C"));}),_r1=40,_r2=10,_r3=new T(function(){return B(_qT(_r2,_r1,_r0));}),_r4=new T(function(){return B(unCStr("20\u00b0 C"));}),_r5=90,_r6=new T(function(){return B(_qT(_r2,_r5,_r4));}),_r7=new T(function(){return B(unCStr("10\u00b0 C"));}),_r8=140,_r9=new T(function(){return B(_qT(_r2,_r8,_r7));}),_ra=190,_rb=new T(function(){return B(unCStr("0\u00b0 C"));}),_rc=new T(function(){return B(_qT(_r2,_ra,_rb));}),_rd=new T(function(){return B(unCStr("-10\u00b0 C"));}),_re=240,_rf=new T(function(){return B(_qT(_r2,_re,_rd));}),_rg=new T(function(){return B(unCStr("-20\u00b0 C"));}),_rh=290,_ri=new T(function(){return B(_qT(_r2,_rh,_rg));}),_rj=new T3(0,0,0,0),_rk=new T(function(){return B(_qF(_rj));}),_rl="strokeStyle",_rm=function(_rn){var _ro=new T(function(){return B(_qy(_rn));});return function(_rp,_){var _rq=__app3(E(_qE),E(_rp),E(_rl),E(_ro));return new F(function(){return _49(_);});};},_rr=new T(function(){return B(_rm(_rj));}),_rs=function(_rt,_){var _ru=B(A1(_qR,_)),_rv=function(_rw,_){var _rx=E(_rw);if(!_rx._){return _2v;}else{var _ry=E(_rt),_rz=_ry.a,_rA=__app1(E(_5x),_ry.b),_rB=B(A2(_qK,_rz,_)),_rC=new T(function(){return B(_pe(_pJ,B(_4B(800,new T(function(){var _rD=B(_39(_rx.a,_p6));if(_rD._==3){return E(_rD.a);}else{return E(_qc);}},1)))));}),_rE=B(_4c(function(_rF,_){return new F(function(){return _qe(_rC,_rF,_);});},_rz,_)),_rG=B(A2(_rr,_rz,_)),_rH=B(_4j(_q6,_rz,_)),_rI=B(A2(_rk,_rz,_)),_rJ=B(A2(_ri,_rz,_)),_rK=B(A2(_rf,_rz,_)),_rL=B(A2(_rc,_rz,_)),_rM=B(A2(_r9,_rz,_)),_rN=B(A2(_r6,_rz,_));return new F(function(){return A2(_r3,_rz,_);});}};return new F(function(){return A(_54,[_2u,_3n,_3n,_48,_4E,_pm,_w,_rv,_]);});},_rO=function(_){var _rP=B(A3(_qM,_2u,_2N,_)),_rQ=B(A3(_2F,_2u,_2M,_)),_rR=E(_rQ);if(!_rR._){return new F(function(){return _2g(_2L,_);});}else{var _rS=E(_rR.a),_rT=__app1(E(_1),_rS);if(!_rT){return new F(function(){return _2g(_2L,_);});}else{var _rU=__app1(E(_0),_rS),_rV=B(_rs(new T2(0,_rU,_rS),_));return _2v;}}},_rW=function(_){return new F(function(){return _rO(_);});};
var hasteMain = function() {B(A(_rW, [0]));};window.onload = hasteMain;