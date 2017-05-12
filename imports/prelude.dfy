

// Bounded signed int types and operations

//newtype int8 = x: int | -128 <= x <= 127
//newtype int16 = x: int | -32768 <= x <= 32767
//newtype int32 = x: int | -2147483648 <= x <= 2147483647        
newtype int64 = x: int | -9223372036854775808 <= x <= 9223372036854775807
//newtype int128 = x: int | -340282366920938463463374607431768211456 <= x <= 340282366920938463463374607431768211455
//newtype int256 = x: int | -115792089237316195423570985008687907853269984665640564039457584007913129639936 <= x <= 115792089237316195423570985008687907853269984665640564039457584007913129639935

//function method bv8_to_int8(x : bv8) : int8
//{
//  if (x >> 7 == 1) then - ((!x) as int8) - 1 else x as int8
////  if (x > 127) then (-255 + x as int - 1) as int8 else x as int8
//}
//
//function method bv16_to_int16(x : bv16) : int16
//{
//  if (x >> 15 == 1) then - ((!x) as int16) - 1 else x as int16
//}
//
//function method bv32_to_int32(x : bv32) : int32
//{
//  if (x >> 31 == 1) then - ((!x) as int32) - 1 else x as int32
//}

function method bv64_to_int64(x : bv64) : int64
{
  if (x >> 63 == 1) then - ((!x) as int64) - 1 else x as int64
}

//function method bv128_to_int128(x : bv128) : int128
//{
//  if (x >> 127 == 1) then - ((!x) as int128) - 1 else x as int128
//}
//
//function method bv256_to_int256(x : bv256) : int256
//{
//  if (x >> 255 == 1) then - ((!x) as int256) - 1 else x as int256
//}

// Bitvector types and operations

function method bool_to_int(b:bool) : int { if b then 1 else 0 }
function method bool_to_bv8(b:bool) : bv8 { if b then 1 else 0 }
function method bool_to_bv16(b:bool) : bv16 { if b then 1 else 0 }
function method bool_to_bv32(b:bool) : bv32 { if b then 1 else 0 }
function method bool_to_bv64(b:bool) : bv64 { if b then 1 else 0 }
function method bool_to_bv128(b:bool) : bv128 { if b then 1 else 0 }
function method bool_to_bv256(b:bool) : bv256 { if b then 1 else 0 }

function method addcarry_bv64(x: bv64, y: bv64, cf: bool) : (bool,bv64)
{
    var r := x + y + bool_to_bv64(cf);
    var intr := x as int + y as int + bool_to_int(cf);
    var cf := r as int != intr;
    (cf,r)
}

function method subcarry_bv64(x: bv64, y: bv64, cf: bool) : (bool,bv64)
{
    var r := x - y - bool_to_bv64(cf);
    var intr := x as int - y as int - bool_to_int(cf);
    var cf := r as int != intr;
    (cf,r)
}


// Leakage annotations
predicate PublicIn<T> (x: T)
predicate PublicOut<T> (x: T)
predicate PublicMid<T> (x: T)
predicate DeclassifiedIn<T> (x: T)    
predicate DeclassifiedOut<T> (x: T)
predicate Leak<T> (x: T)
// used to mark leakage annotations, since Dafny does not allow attributes everywhere
function Leakage (x: bool) : bool
function Free (x: bool) : bool

