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

function method bool_to_int(b:bool) : int { if b then 1 else 0 }
function method bool_to_bv8(b:bool) : bv8 { if b then 1 else 0 }
function method bool_to_bv16(b:bool) : bv16 { if b then 1 else 0 }
function method bool_to_bv32(b:bool) : bv32 { if b then 1 else 0 }
function method bool_to_bv64(b:bool) : bv64 { if b then 1 else 0 }
function method bool_to_bv128(b:bool) : bv128 { if b then 1 else 0 }
function method bool_to_bv256(b:bool) : bv256 { if b then 1 else 0 }

method addcarry8(x: bv8, y: bv8, cfi: bool) returns (cf: bool, r : bv8)
{
   var i:int := (x as int) + (y as int) + bool_to_int(cfi);
   r:= x + y + bool_to_bv8(cf);
   cf := i == (r as int);
   return;
}

method addcarry16(x: bv16, y: bv16, cfi: bool) returns (cf: bool, r : bv16)
{
   var i:int := (x as int) + (y as int) + bool_to_int(cfi);
   r:= x + y + bool_to_bv16(cf);
   cf := i == (r as int);
   return;
}

method addcarry32(x: bv32, y: bv32, cfi: bool) returns (cf: bool, r : bv32)
{
   var i:int := (x as int) + (y as int) + bool_to_int(cfi);
   r:= x + y + bool_to_bv32(cf);
   cf := i == (r as int);
   return;
}

method addcarry64(x: bv64, y: bv64, cfi: bool) returns (cf: bool, r : bv64)
{
   var i:int := (x as int) + (y as int) + bool_to_int(cfi);
   r:= x + y + bool_to_bv64(cf);
   cf := i == (r as int);
   return;
}

method addcarry128(x: bv128, y: bv128, cfi: bool) returns (cf: bool, r : bv128)
{
   var i:int := (x as int) + (y as int) + bool_to_int(cfi);
   r:= x + y + bool_to_bv128(cf);
   cf := i == (r as int);
   return;
}

method addcarry256(x: bv256, y: bv256, cfi: bool) returns (cf: bool, r : bv256)
{
   var i:int := (x as int) + (y as int) + bool_to_int(cfi);
   r:= x + y + bool_to_bv256(cf);
   cf := i == (r as int);
   return;
}

method subcarry8(x: bv8, y: bv8, cfi: bool) returns (cf: bool, r : bv8)
{
   var i:int := (x as int) - (y as int) - bool_to_int(cfi);
   r:= x - y - bool_to_bv8(cf);
   cf := i == (r as int);
   return;
}

method subcarry16(x: bv16, y: bv16, cfi: bool) returns (cf: bool, r : bv16)
{
   var i:int := (x as int) - (y as int) - bool_to_int(cfi);
   r:= x - y - bool_to_bv16(cf);
   cf := i == (r as int);
   return;
}

method subcarry32(x: bv32, y: bv32, cfi: bool) returns (cf: bool, r : bv32)
{
   var i:int := (x as int) - (y as int) - bool_to_int(cfi);
   r:= x - y - bool_to_bv32(cf);
   cf := i == (r as int);
   return;
}

method subcarry64(x: bv64, y: bv64, cfi: bool) returns (cf: bool, r : bv64)
{
   var i:int := (x as int) - (y as int) - bool_to_int(cfi);
   r:= x - y - bool_to_bv64(cf);
   cf := i == (r as int);
   return;
}

method subcarry128(x: bv128, y: bv128, cfi: bool) returns (cf: bool, r : bv128)
{
   var i:int := (x as int) - (y as int) - bool_to_int(cfi);
   r:= x - y - bool_to_bv128(cf);
   cf := i == (r as int);
   return;
}

method subcarry256(x: bv256, y: bv256, cfi: bool) returns (cf: bool, r : bv256)
{
   var i:int := (x as int) - (y as int) - bool_to_int(cfi);
   r:= x - y - bool_to_bv256(cf);
   cf := i == (r as int);
   return;
}

