
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

datatype Vec<T> {
    Vec(v: [int]T, l: int)
}

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := v->l;
    Vec(v->v[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v->v[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    v->l
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    v->l == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := v->l - 1;
    Vec(v->v[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := v->l - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v->v[j] else v->v[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := v1->l, v1->v, v2->l, v2->v;
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := v->l;
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v->v[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v->v[i := elem], v->l)
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(m[i := m[j]][j := m[i]], v->l))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := v->l;
    (exists i: int :: InRangeVec(v, i) && v->v[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

datatype Multiset<T> {
    Multiset(v: [T]int, l: int)
}

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    s->l
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := s->l;
    (var cnt := s->v[v];
    Multiset(s->v[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := s1->l;
    (var len2 := s2->l;
    Multiset((lambda v:T :: s1->v[v]-s2->v[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (s->l == 0) &&
    (forall v: T :: s->v[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (s1->l <= s2->l) &&
    (forall v: T :: s1->v[v] <= s2->v[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    s->v[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int)
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    t->v[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    t->l
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    t->e[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(t->v[k := v], t->e, t->l)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(t->v[k := v], t->e[k := true], t->l + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(t->v, t->e[k := false], t->l - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.


// Prover
procedure {:inline 1} $ShlBvBv256From8(src1: bv256, src2: bv8) returns (dst: bv256) {
    call dst := $ShlBv256From8(src1, src2);
}

procedure {:inline 1} $0_prover_requires(p: bool) {
    assume p;
}

type $1_integer_Integer = int;
function {:inline} $IsValid'$1_integer_Integer'(x: int): bool {
    true
}
function {:inline} $IsEqual'$1_integer_Integer'(x: int, y: int): bool {
    x == y
}
procedure {:inline 1} $0_prover_type_inv'$1_integer_Integer'(x: int) returns (y: bool) {
    y := true;
}procedure {:inline 1} $1_integer_from_u8(x: int) returns (y: int) {
    y := x;
}
procedure {:inline 1} $1_integer_from_u16(x: int) returns (y: int) {
    y := x;
}
procedure {:inline 1} $1_integer_from_u32(x: int) returns (y: int) {
    y := x;
}
procedure {:inline 1} $1_integer_from_u64(x: int) returns (y: int) {
    y := x;
}
procedure {:inline 1} $1_integer_from_u128(x: int) returns (y: int) {
    y := x;
}
procedure {:inline 1} $1_integer_from_u256(x: int) returns (y: int) {
    y := x;
}
procedure {:inline 1} $1_integer_to_u8(x: int) returns (y: int) {
    y := x mod 256;
}
procedure {:inline 1} $1_integer_to_u16(x: int) returns (y: int) {
    y := x mod 65536;
}
procedure {:inline 1} $1_integer_to_u32(x: int) returns (y: int) {
    y := x mod 4294967296;
}
procedure {:inline 1} $1_integer_to_u64(x: int) returns (y: int) {
    y := x mod 18446744073709551616;
}
procedure {:inline 1} $1_integer_to_u128(x: int) returns (y: int) {
    y := x mod 340282366920938463463374607431768211456;
}
procedure {:inline 1} $1_integer_to_u256(x: int) returns (y: int) {
    y := x mod 115792089237316195423570985008687907853269984665640564039457584007913129639936;
}

procedure {:inline 1} $1_integer_add(x: int, y: int) returns (z: int) {
    z := x + y;
}
procedure {:inline 1} $1_integer_sub(x: int, y: int) returns (z: int) {
    z := x - y;
}
procedure {:inline 1} $1_integer_neg(x: int) returns (z: int) {
    z := -x;
}
procedure {:inline 1} $1_integer_mul(x: int, y: int) returns (z: int) {
    z := x * y;
}
procedure {:inline 1} $1_integer_div(x: int, y: int) returns (z: int) {
    z := x div y;
}
procedure {:inline 1} $1_integer_mod(x: int, y: int) returns (z: int) {
    z := x mod y;
}
procedure {:inline 1} $1_integer_pow(x: int, y: int) returns (z: int) {
    z := $pow(x, y);
}
function $andInt(x: int, y: int) returns (int);
function $orInt(x: int, y: int) returns (int);
function $xorInt(x: int, y: int) returns (int);
function $notInt(x: int) returns (int);
procedure {:inline 1} $1_integer_bit_and(x: int, y: int) returns (z: int) {
    z := $andInt(x, y);
}
procedure {:inline 1} $1_integer_bit_or(x: int, y: int) returns (z: int) {
    z := $orInt(x, y);
}
procedure {:inline 1} $1_integer_bit_xor(x: int, y: int) returns (z: int) {
    z := $xorInt(x, y);
}
procedure {:inline 1} $1_integer_bit_not(x: int) returns (z: int) {
    z := $notInt(x);
}
procedure {:inline 1} $1_integer_lt(x: int, y: int) returns (z: bool) {
    z := x < y;
}
procedure {:inline 1} $1_integer_gt(x: int, y: int) returns (z: bool) {
    z := x > y;
}
procedure {:inline 1} $1_integer_lte(x: int, y: int) returns (z: bool) {
    z := x <= y;
}
procedure {:inline 1} $1_integer_gte(x: int, y: int) returns (z: bool) {
    z := x >= y;
}
procedure {:inline 1} $1_integer_div_real(x: int, y: int) returns (z: real) {
    z := x / y;
}

function $to_u8(x: int): int {
    x mod 256
}
function $to_u16(x: int): int {
    x mod 65536
}
function $to_u32(x: int): int {
    x mod 4294967296
}
function $to_u64(x: int): int {
    x mod 18446744073709551616
}
function $to_u128(x: int): int {
    x mod 340282366920938463463374607431768211456
}
function $to_u256(x: int): int {
    x mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $to_i8(x: int): int {(
    var y := x mod 256;
    if y < 256 - y then
        y
    else
        y - 256
)}
function $to_i16(x: int): int {(
    var y := x mod 65536;
    if y < 65536 - y then
        y
    else
        y - 65536
)}
function $to_i32(x: int): int {(
    var y := x mod 4294967296;
    if y < 4294967296 - y then
        y
    else
        y - 4294967296
)}
function $to_i64(x: int): int {(
    var y := x mod 18446744073709551616;
    if y < 18446744073709551616 - y then
        y
    else
        y - 18446744073709551616
)}
function $to_i128(x: int): int {(
    var y := x mod 340282366920938463463374607431768211456;
    if y < 340282366920938463463374607431768211456 - y then
        y
    else
        y - 340282366920938463463374607431768211456
)}
function $to_i256(x: int): int {(
    var y := x mod 115792089237316195423570985008687907853269984665640564039457584007913129639936;
    if y < 115792089237316195423570985008687907853269984665640564039457584007913129639936 - y then
        y
    else
        y - 115792089237316195423570985008687907853269984665640564039457584007913129639936
)}

type $1_real_Real = real;
function {:inline} $IsValid'$1_real_Real'(x: real): bool {
    true
}
function {:inline} $IsEqual'$1_real_Real'(x: real, y: real): bool {
    x == y
}
procedure {:inline 1} $0_prover_type_inv'$1_real_Real'(x: real) returns (y: bool) {
    y := true;
}
procedure {:inline 1} $1_real_from_integer(x: int) returns (y: real) {
    y := real(x);
}
procedure {:inline 1} $1_real_to_integer(x: real) returns (y: int) {
    y := int(x);
}
procedure {:inline 1} $1_real_add(x: real, y: real) returns (z: real) {
    z := x + y;
}
procedure {:inline 1} $1_real_sub(x: real, y: real) returns (z: real) {
    z := x - y;
}
procedure {:inline 1} $1_real_neg(x: real) returns (z: real) {
    z := -x;
}
procedure {:inline 1} $1_real_mul(x: real, y: real) returns (z: real) {
    z := x * y;
}
procedure {:inline 1} $1_real_div(x: real, y: real) returns (z: real) {
    z := x / y;
}
procedure {:inline 1} $1_real_exp(x: real, y: real) returns (z: real) {
    z := x ** y;
}
procedure {:inline 1} $1_real_lt(x: real, y: real) returns (z: bool) {
    z := x < y;
}
procedure {:inline 1} $1_real_gt(x: real, y: real) returns (z: bool) {
    z := x > y;
}
procedure {:inline 1} $1_real_lte(x: real, y: real) returns (z: bool) {
    z := x <= y;
}
procedure {:inline 1} $1_real_gte(x: real, y: real) returns (z: bool) {
    z := x >= y;
}

// temporary stuff
procedure {:inline 1} $0_prover_requires_begin() {}
procedure {:inline 1} $0_prover_requires_end() {}
procedure {:inline 1} $0_prover_ensures_begin() {}
procedure {:inline 1} $0_prover_ensures_end() {}
procedure {:inline 1} $0_prover_aborts_begin() {}
procedure {:inline 1} $0_prover_aborts_end() {}
procedure {:inline 1} $0_prover_invariant_begin() {}
procedure {:inline 1} $0_prover_invariant_end() {}


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

const $POW_2_8: int;
axiom $POW_2_8 == 256;
const $POW_2_16: int;
axiom $POW_2_16 == 65536;
const $POW_2_32: int;
axiom $POW_2_32 == 4294967296;
const $POW_2_64: int;
axiom $POW_2_64 == 18446744073709551616;
const $POW_2_128: int;
axiom $POW_2_128 == 340282366920938463463374607431768211456;
const $POW_2_256: int;
axiom $POW_2_256 == 115792089237316195423570985008687907853269984665640564039457584007913129639936;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsdiv"} $SDiv'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsrem"} $SMod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvashr"} $AShr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv8'(v: bv8) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function $andInt'u8'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_8, y mod $POW_2_8)
}
function $andInt'i8'(x: int, y: int) returns (int) {
    $andInt($to_i8(x), $to_i8(y))
}
axiom (forall x, y : int :: {$andInt'u8'(x, y)}
    $andInt'u8'(x, y) == $andInt(x, y) mod $POW_2_8
);
axiom (forall x, y : int :: {$andInt'u8'(x, y)}
    0 <= $andInt'u8'(x, y) && $andInt'u8'(x, y) < $POW_2_8
);
axiom (forall x, y : int :: {$andInt'u8'(x, y)}
    $to_i8($andInt'u8'(x, y)) == $andInt'i8'(x, y)
);
function $orInt'u8'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_8, y mod $POW_2_8)
}
function $orInt'i8'(x: int, y: int) returns (int) {
    $orInt($to_i8(x), $to_i8(y))
}
axiom (forall x, y : int :: {$orInt'u8'(x, y)}
    $orInt'u8'(x, y) == $orInt(x, y) mod $POW_2_8
);
axiom (forall x, y : int :: {$orInt'u8'(x, y)}
    0 <= $orInt'u8'(x, y) && $orInt'u8'(x, y) < $POW_2_8
);
axiom (forall x, y : int :: {$orInt'u8'(x, y)}
    $to_i8($orInt'u8'(x, y)) == $orInt'i8'(x, y)
);
function $xorInt'u8'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_8, y mod $POW_2_8)
}
function $xorInt'i8'(x: int, y: int) returns (int) {
    $xorInt($to_i8(x), $to_i8(y))
}
axiom (forall x, y: int :: {$xorInt'u8'(x, y)}
    $xorInt'u8'(x, y) == $xorInt(x, y) mod $POW_2_8
);
axiom (forall x, y: int :: {$xorInt'u8'(x, y)}
    0 <= $xorInt'u8'(x, y) && $xorInt'u8'(x, y) < $POW_2_8
);
axiom (forall x, y : int :: {$xorInt'u8'(x, y)}
    $to_i8($xorInt'u8'(x, y)) == $xorInt'i8'(x, y)
);

procedure {:inline 1} $AndInt'u8'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u8'(src1, src2);
}
procedure {:inline 1} $OrInt'u8'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u8'(src1, src2);
}
procedure {:inline 1} $XorInt'u8'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u8'(src1, src2);
}

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsdiv"} $SDiv'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsrem"} $SMod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvashr"} $AShr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv16'(v: bv16) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function $andInt'u16'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_16, y mod $POW_2_16)
}
function $andInt'i16'(x: int, y: int) returns (int) {
    $andInt($to_i16(x), $to_i16(y))
}
axiom (forall x, y : int :: {$andInt'u16'(x, y)}
    $andInt'u16'(x, y) == $andInt(x, y) mod $POW_2_16
);
axiom (forall x, y : int :: {$andInt'u16'(x, y)}
    0 <= $andInt'u16'(x, y) && $andInt'u16'(x, y) < $POW_2_16
);
axiom (forall x, y : int :: {$andInt'u16'(x, y)}
    $to_i16($andInt'u16'(x, y)) == $andInt'i16'(x, y)
);
function $orInt'u16'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_16, y mod $POW_2_16)
}
function $orInt'i16'(x: int, y: int) returns (int) {
    $orInt($to_i16(x), $to_i16(y))
}
axiom (forall x, y : int :: {$orInt'u16'(x, y)}
    $orInt'u16'(x, y) == $orInt(x, y) mod $POW_2_16
);
axiom (forall x, y : int :: {$orInt'u16'(x, y)}
    0 <= $orInt'u16'(x, y) && $orInt'u16'(x, y) < $POW_2_16
);
axiom (forall x, y : int :: {$orInt'u16'(x, y)}
    $to_i16($orInt'u16'(x, y)) == $orInt'i16'(x, y)
);
function $xorInt'u16'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_16, y mod $POW_2_16)
}
function $xorInt'i16'(x: int, y: int) returns (int) {
    $xorInt($to_i16(x), $to_i16(y))
}
axiom (forall x, y: int :: {$xorInt'u16'(x, y)}
    $xorInt'u16'(x, y) == $xorInt(x, y) mod $POW_2_16
);
axiom (forall x, y: int :: {$xorInt'u16'(x, y)}
    0 <= $xorInt'u16'(x, y) && $xorInt'u16'(x, y) < $POW_2_16
);
axiom (forall x, y : int :: {$xorInt'u16'(x, y)}
    $to_i16($xorInt'u16'(x, y)) == $xorInt'i16'(x, y)
);

procedure {:inline 1} $AndInt'u16'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u16'(src1, src2);
}
procedure {:inline 1} $OrInt'u16'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u16'(src1, src2);
}
procedure {:inline 1} $XorInt'u16'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u16'(src1, src2);
}

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsdiv"} $SDiv'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsrem"} $SMod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvashr"} $AShr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,4294967295bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv32'(v: bv32) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 4294967295) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function $andInt'u32'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_32, y mod $POW_2_32)
}
function $andInt'i32'(x: int, y: int) returns (int) {
    $andInt($to_i32(x), $to_i32(y))
}
axiom (forall x, y : int :: {$andInt'u32'(x, y)}
    $andInt'u32'(x, y) == $andInt(x, y) mod $POW_2_32
);
axiom (forall x, y : int :: {$andInt'u32'(x, y)}
    0 <= $andInt'u32'(x, y) && $andInt'u32'(x, y) < $POW_2_32
);
axiom (forall x, y : int :: {$andInt'u32'(x, y)}
    $to_i32($andInt'u32'(x, y)) == $andInt'i32'(x, y)
);
function $orInt'u32'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_32, y mod $POW_2_32)
}
function $orInt'i32'(x: int, y: int) returns (int) {
    $orInt($to_i32(x), $to_i32(y))
}
axiom (forall x, y : int :: {$orInt'u32'(x, y)}
    $orInt'u32'(x, y) == $orInt(x, y) mod $POW_2_32
);
axiom (forall x, y : int :: {$orInt'u32'(x, y)}
    0 <= $orInt'u32'(x, y) && $orInt'u32'(x, y) < $POW_2_32
);
axiom (forall x, y : int :: {$orInt'u32'(x, y)}
    $to_i32($orInt'u32'(x, y)) == $orInt'i32'(x, y)
);
function $xorInt'u32'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_32, y mod $POW_2_32)
}
function $xorInt'i32'(x: int, y: int) returns (int) {
    $xorInt($to_i32(x), $to_i32(y))
}
axiom (forall x, y: int :: {$xorInt'u32'(x, y)}
    $xorInt'u32'(x, y) == $xorInt(x, y) mod $POW_2_32
);
axiom (forall x, y: int :: {$xorInt'u32'(x, y)}
    0 <= $xorInt'u32'(x, y) && $xorInt'u32'(x, y) < $POW_2_32
);
axiom (forall x, y : int :: {$xorInt'u32'(x, y)}
    $to_i32($xorInt'u32'(x, y)) == $xorInt'i32'(x, y)
);

procedure {:inline 1} $AndInt'u32'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u32'(src1, src2);
}
procedure {:inline 1} $OrInt'u32'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u32'(src1, src2);
}
procedure {:inline 1} $XorInt'u32'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u32'(src1, src2);
}

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsdiv"} $SDiv'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsrem"} $SMod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvashr"} $AShr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv64'(v: bv64) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function $andInt'u64'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_64, y mod $POW_2_64)
}
function $andInt'i64'(x: int, y: int) returns (int) {
    $andInt($to_i64(x), $to_i64(y))
}
axiom (forall x, y : int :: {$andInt'u64'(x, y)}
    $andInt'u64'(x, y) == $andInt(x, y) mod $POW_2_64
);
axiom (forall x, y : int :: {$andInt'u64'(x, y)}
    0 <= $andInt'u64'(x, y) && $andInt'u64'(x, y) < $POW_2_64
);
axiom (forall x, y : int :: {$andInt'u64'(x, y)}
    $to_i64($andInt'u64'(x, y)) == $andInt'i64'(x, y)
);
function $orInt'u64'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_64, y mod $POW_2_64)
}
function $orInt'i64'(x: int, y: int) returns (int) {
    $orInt($to_i64(x), $to_i64(y))
}
axiom (forall x, y : int :: {$orInt'u64'(x, y)}
    $orInt'u64'(x, y) == $orInt(x, y) mod $POW_2_64
);
axiom (forall x, y : int :: {$orInt'u64'(x, y)}
    0 <= $orInt'u64'(x, y) && $orInt'u64'(x, y) < $POW_2_64
);
axiom (forall x, y : int :: {$orInt'u64'(x, y)}
    $to_i64($orInt'u64'(x, y)) == $orInt'i64'(x, y)
);
function $xorInt'u64'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_64, y mod $POW_2_64)
}
function $xorInt'i64'(x: int, y: int) returns (int) {
    $xorInt($to_i64(x), $to_i64(y))
}
axiom (forall x, y: int :: {$xorInt'u64'(x, y)}
    $xorInt'u64'(x, y) == $xorInt(x, y) mod $POW_2_64
);
axiom (forall x, y: int :: {$xorInt'u64'(x, y)}
    0 <= $xorInt'u64'(x, y) && $xorInt'u64'(x, y) < $POW_2_64
);
axiom (forall x, y : int :: {$xorInt'u64'(x, y)}
    $to_i64($xorInt'u64'(x, y)) == $xorInt'i64'(x, y)
);

procedure {:inline 1} $AndInt'u64'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u64'(src1, src2);
}
procedure {:inline 1} $OrInt'u64'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u64'(src1, src2);
}
procedure {:inline 1} $XorInt'u64'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u64'(src1, src2);
}

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsdiv"} $SDiv'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsrem"} $SMod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvashr"} $AShr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv128'(v: bv128) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function $andInt'u128'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_128, y mod $POW_2_128)
}
function $andInt'i128'(x: int, y: int) returns (int) {
    $andInt($to_i128(x), $to_i128(y))
}
axiom (forall x, y : int :: {$andInt'u128'(x, y)}
    $andInt'u128'(x, y) == $andInt(x, y) mod $POW_2_128
);
axiom (forall x, y : int :: {$andInt'u128'(x, y)}
    0 <= $andInt'u128'(x, y) && $andInt'u128'(x, y) < $POW_2_128
);
axiom (forall x, y : int :: {$andInt'u128'(x, y)}
    $to_i128($andInt'u128'(x, y)) == $andInt'i128'(x, y)
);
function $orInt'u128'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_128, y mod $POW_2_128)
}
function $orInt'i128'(x: int, y: int) returns (int) {
    $orInt($to_i128(x), $to_i128(y))
}
axiom (forall x, y : int :: {$orInt'u128'(x, y)}
    $orInt'u128'(x, y) == $orInt(x, y) mod $POW_2_128
);
axiom (forall x, y : int :: {$orInt'u128'(x, y)}
    0 <= $orInt'u128'(x, y) && $orInt'u128'(x, y) < $POW_2_128
);
axiom (forall x, y : int :: {$orInt'u128'(x, y)}
    $to_i128($orInt'u128'(x, y)) == $orInt'i128'(x, y)
);
function $xorInt'u128'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_128, y mod $POW_2_128)
}
function $xorInt'i128'(x: int, y: int) returns (int) {
    $xorInt($to_i128(x), $to_i128(y))
}
axiom (forall x, y: int :: {$xorInt'u128'(x, y)}
    $xorInt'u128'(x, y) == $xorInt(x, y) mod $POW_2_128
);
axiom (forall x, y: int :: {$xorInt'u128'(x, y)}
    0 <= $xorInt'u128'(x, y) && $xorInt'u128'(x, y) < $POW_2_128
);
axiom (forall x, y : int :: {$xorInt'u128'(x, y)}
    $to_i128($xorInt'u128'(x, y)) == $xorInt'i128'(x, y)
);

procedure {:inline 1} $AndInt'u128'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u128'(src1, src2);
}
procedure {:inline 1} $OrInt'u128'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u128'(src1, src2);
}
procedure {:inline 1} $XorInt'u128'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u128'(src1, src2);
}

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsdiv"} $SDiv'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsrem"} $SMod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvashr"} $AShr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv256'(v: bv256) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

function $andInt'u256'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_256, y mod $POW_2_256)
}
function $andInt'i256'(x: int, y: int) returns (int) {
    $andInt($to_i256(x), $to_i256(y))
}
axiom (forall x, y : int :: {$andInt'u256'(x, y)}
    $andInt'u256'(x, y) == $andInt(x, y) mod $POW_2_256
);
axiom (forall x, y : int :: {$andInt'u256'(x, y)}
    0 <= $andInt'u256'(x, y) && $andInt'u256'(x, y) < $POW_2_256
);
axiom (forall x, y : int :: {$andInt'u256'(x, y)}
    $to_i256($andInt'u256'(x, y)) == $andInt'i256'(x, y)
);
function $orInt'u256'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_256, y mod $POW_2_256)
}
function $orInt'i256'(x: int, y: int) returns (int) {
    $orInt($to_i256(x), $to_i256(y))
}
axiom (forall x, y : int :: {$orInt'u256'(x, y)}
    $orInt'u256'(x, y) == $orInt(x, y) mod $POW_2_256
);
axiom (forall x, y : int :: {$orInt'u256'(x, y)}
    0 <= $orInt'u256'(x, y) && $orInt'u256'(x, y) < $POW_2_256
);
axiom (forall x, y : int :: {$orInt'u256'(x, y)}
    $to_i256($orInt'u256'(x, y)) == $orInt'i256'(x, y)
);
function $xorInt'u256'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_256, y mod $POW_2_256)
}
function $xorInt'i256'(x: int, y: int) returns (int) {
    $xorInt($to_i256(x), $to_i256(y))
}
axiom (forall x, y: int :: {$xorInt'u256'(x, y)}
    $xorInt'u256'(x, y) == $xorInt(x, y) mod $POW_2_256
);
axiom (forall x, y: int :: {$xorInt'u256'(x, y)}
    0 <= $xorInt'u256'(x, y) && $xorInt'u256'(x, y) < $POW_2_256
);
axiom (forall x, y : int :: {$xorInt'u256'(x, y)}
    $to_i256($xorInt'u256'(x, y)) == $xorInt'i256'(x, y)
);

procedure {:inline 1} $AndInt'u256'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u256'(src1, src2);
}
procedure {:inline 1} $OrInt'u256'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u256'(src1, src2);
}
procedure {:inline 1} $XorInt'u256'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u256'(src1, src2);
}

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function {:inline} $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bool'(x: bool) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u8'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u16'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u32'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u64'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u128'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u256'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'num'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'address'(x: int) returns (y: bool) {
    y := true;
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    $SpecGlobal(s: string),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 4294967295bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 4294967295bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 4294967295bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T

// ==================================================================================
// Native Option

// ----------------------------------------------------------------------------------
// Native Option implementation for element type `vec'u8'`

function $IsValid'$1_option_Option'vec'u8'''(opt: $1_option_Option'vec'u8''): bool {
    $IsValid'vec'vec'u8'''(opt->$vec) &&
    (LenVec(opt->$vec) == 0 || LenVec(opt->$vec) == 1)
}



// ----------------------------------------------------------------------------------
// Native Option implementation for element type `$1_string_String`

function $IsValid'$1_option_Option'$1_string_String''(opt: $1_option_Option'$1_string_String'): bool {
    $IsValid'vec'$1_string_String''(opt->$vec) &&
    (LenVec(opt->$vec) == 0 || LenVec(opt->$vec) == 1)
}



// ----------------------------------------------------------------------------------
// Native Option implementation for element type `$2_table_vec_TableVec'vec'u8''`

function $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(opt: $1_option_Option'$2_table_vec_TableVec'vec'u8'''): bool {
    $IsValid'vec'$2_table_vec_TableVec'vec'u8''''(opt->$vec) &&
    (LenVec(opt->$vec) == 0 || LenVec(opt->$vec) == 1)
}




// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_string_String`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_string_String''(v1: Vec ($1_string_String), v2: Vec ($1_string_String)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_string_String'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_string_String''(v: Vec ($1_string_String), prefix: Vec ($1_string_String)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_string_String'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_string_String''(v: Vec ($1_string_String), suffix: Vec ($1_string_String)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_string_String'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_string_String''(v: Vec ($1_string_String)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_string_String'(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'$1_string_String''(v: Vec ($1_string_String)) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'$1_string_String'(v: Vec ($1_string_String), e: $1_string_String): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_string_String'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_string_String'(v: Vec ($1_string_String), e: $1_string_String): int;
axiom (forall v: Vec ($1_string_String), e: $1_string_String:: {$IndexOfVec'$1_string_String'(v, e)}
    (var i := $IndexOfVec'$1_string_String'(v, e);
     if (!$ContainsVec'$1_string_String'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_string_String'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_string_String'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_string_String'(v: Vec ($1_string_String)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_string_String'(): Vec ($1_string_String) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_string_String'() returns (v: Vec ($1_string_String)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_string_String'(): Vec ($1_string_String) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_string_String'(v: Vec ($1_string_String)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_string_String'(m: $Mutation (Vec ($1_string_String)), val: $1_string_String) returns (m': $Mutation (Vec ($1_string_String))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_string_String'(v: Vec ($1_string_String), val: $1_string_String): Vec ($1_string_String) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_string_String'(m: $Mutation (Vec ($1_string_String))) returns (e: $1_string_String, m': $Mutation (Vec ($1_string_String))) {
    var v: Vec ($1_string_String);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$1_string_String'(m: $Mutation (Vec ($1_string_String)), other: Vec ($1_string_String)) returns (m': $Mutation (Vec ($1_string_String))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_string_String'(m: $Mutation (Vec ($1_string_String))) returns (m': $Mutation (Vec ($1_string_String))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_string_String'(m: $Mutation (Vec ($1_string_String)), other: Vec ($1_string_String)) returns (m': $Mutation (Vec ($1_string_String))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_string_String'(m: $Mutation (Vec ($1_string_String)), new_len: int) returns (v: (Vec ($1_string_String)), m': $Mutation (Vec ($1_string_String))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$1_string_String'(m: $Mutation (Vec ($1_string_String)), new_len: int) returns (v: (Vec ($1_string_String)), m': $Mutation (Vec ($1_string_String))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_string_String'(m: $Mutation (Vec ($1_string_String)), left: int, right: int) returns (m': $Mutation (Vec ($1_string_String))) {
    var left_vec: Vec ($1_string_String);
    var mid_vec: Vec ($1_string_String);
    var right_vec: Vec ($1_string_String);
    var v: Vec ($1_string_String);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$1_string_String'(m: $Mutation (Vec ($1_string_String)), rot: int) returns (n: int, m': $Mutation (Vec ($1_string_String))) {
    var v: Vec ($1_string_String);
    var len: int;
    var left_vec: Vec ($1_string_String);
    var right_vec: Vec ($1_string_String);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$1_string_String'(m: $Mutation (Vec ($1_string_String)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_string_String))) {
    var left_vec: Vec ($1_string_String);
    var mid_vec: Vec ($1_string_String);
    var right_vec: Vec ($1_string_String);
    var mid_left_vec: Vec ($1_string_String);
    var mid_right_vec: Vec ($1_string_String);
    var v: Vec ($1_string_String);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$1_string_String'(m: $Mutation (Vec ($1_string_String)), i: int, e: $1_string_String) returns (m': $Mutation (Vec ($1_string_String))) {
    var left_vec: Vec ($1_string_String);
    var right_vec: Vec ($1_string_String);
    var v: Vec ($1_string_String);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$1_string_String'(v: Vec ($1_string_String)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_string_String'(v: Vec ($1_string_String)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_string_String'(v: Vec ($1_string_String), i: int) returns (dst: $1_string_String) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_string_String'(v: Vec ($1_string_String), i: int): $1_string_String {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_string_String'(m: $Mutation (Vec ($1_string_String)), index: int)
returns (dst: $Mutation ($1_string_String), m': $Mutation (Vec ($1_string_String)))
{
    var v: Vec ($1_string_String);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_string_String'(v: Vec ($1_string_String), i: int): $1_string_String {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_string_String'(v: Vec ($1_string_String)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_string_String'(m: $Mutation (Vec ($1_string_String)), i: int, j: int) returns (m': $Mutation (Vec ($1_string_String)))
{
    var v: Vec ($1_string_String);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_string_String'(v: Vec ($1_string_String), i: int, j: int): Vec ($1_string_String) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_string_String'(m: $Mutation (Vec ($1_string_String)), i: int) returns (e: $1_string_String, m': $Mutation (Vec ($1_string_String)))
{
    var v: Vec ($1_string_String);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_string_String'(m: $Mutation (Vec ($1_string_String)), i: int) returns (e: $1_string_String, m': $Mutation (Vec ($1_string_String)))
{
    var len: int;
    var v: Vec ($1_string_String);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_string_String'(v: Vec ($1_string_String), e: $1_string_String) returns (res: bool)  {
    res := $ContainsVec'$1_string_String'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_string_String'(v: Vec ($1_string_String), e: $1_string_String) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_string_String'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'$1_string_String'(v: Vec ($1_string_String), n: int) returns (res: Vec ($1_string_String)) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'$1_string_String'(v: Vec ($1_string_String), n: int): Vec ($1_string_String) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'$1_string_String'(v: Vec ($1_string_String), n: int) returns (res: Vec ($1_string_String)) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'$1_string_String'(v: Vec ($1_string_String), n: int): Vec ($1_string_String) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$2_table_vec_TableVec'vec'u8''`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$2_table_vec_TableVec'vec'u8''''(v1: Vec ($2_table_vec_TableVec'vec'u8''), v2: Vec ($2_table_vec_TableVec'vec'u8'')): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$2_table_vec_TableVec'vec'u8'''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$2_table_vec_TableVec'vec'u8''''(v: Vec ($2_table_vec_TableVec'vec'u8''), prefix: Vec ($2_table_vec_TableVec'vec'u8'')): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$2_table_vec_TableVec'vec'u8'''(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$2_table_vec_TableVec'vec'u8''''(v: Vec ($2_table_vec_TableVec'vec'u8''), suffix: Vec ($2_table_vec_TableVec'vec'u8'')): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$2_table_vec_TableVec'vec'u8'''(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$2_table_vec_TableVec'vec'u8''''(v: Vec ($2_table_vec_TableVec'vec'u8'')): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$2_table_vec_TableVec'vec'u8'''(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'$2_table_vec_TableVec'vec'u8''''(v: Vec ($2_table_vec_TableVec'vec'u8'')) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), e: $2_table_vec_TableVec'vec'u8''): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_table_vec_TableVec'vec'u8'''(ReadVec(v, i), e))
}

function $IndexOfVec'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), e: $2_table_vec_TableVec'vec'u8''): int;
axiom (forall v: Vec ($2_table_vec_TableVec'vec'u8''), e: $2_table_vec_TableVec'vec'u8'':: {$IndexOfVec'$2_table_vec_TableVec'vec'u8'''(v, e)}
    (var i := $IndexOfVec'$2_table_vec_TableVec'vec'u8'''(v, e);
     if (!$ContainsVec'$2_table_vec_TableVec'vec'u8'''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_table_vec_TableVec'vec'u8'''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$2_table_vec_TableVec'vec'u8'''(ReadVec(v, j), e))));


function {:inline} $RangeVec'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8'')): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$2_table_vec_TableVec'vec'u8'''(): Vec ($2_table_vec_TableVec'vec'u8'') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$2_table_vec_TableVec'vec'u8'''() returns (v: Vec ($2_table_vec_TableVec'vec'u8'')) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$2_table_vec_TableVec'vec'u8'''(): Vec ($2_table_vec_TableVec'vec'u8'') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8'')) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), val: $2_table_vec_TableVec'vec'u8'') returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), val: $2_table_vec_TableVec'vec'u8''): Vec ($2_table_vec_TableVec'vec'u8'') {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) returns (e: $2_table_vec_TableVec'vec'u8'', m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), other: Vec ($2_table_vec_TableVec'vec'u8'')) returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), other: Vec ($2_table_vec_TableVec'vec'u8'')) returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), new_len: int) returns (v: (Vec ($2_table_vec_TableVec'vec'u8'')), m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), new_len: int) returns (v: (Vec ($2_table_vec_TableVec'vec'u8'')), m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), left: int, right: int) returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var left_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var mid_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var right_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), rot: int) returns (n: int, m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    var len: int;
    var left_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var right_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var left_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var mid_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var right_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var mid_left_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var mid_right_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), i: int, e: $2_table_vec_TableVec'vec'u8'') returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8''))) {
    var left_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var right_vec: Vec ($2_table_vec_TableVec'vec'u8'');
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8'')) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8'')): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), i: int) returns (dst: $2_table_vec_TableVec'vec'u8'') {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), i: int): $2_table_vec_TableVec'vec'u8'' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), index: int)
returns (dst: $Mutation ($2_table_vec_TableVec'vec'u8''), m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')))
{
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), i: int): $2_table_vec_TableVec'vec'u8'' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8'')) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), i: int, j: int) returns (m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')))
{
    var v: Vec ($2_table_vec_TableVec'vec'u8'');
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), i: int, j: int): Vec ($2_table_vec_TableVec'vec'u8'') {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), i: int) returns (e: $2_table_vec_TableVec'vec'u8'', m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')))
{
    var v: Vec ($2_table_vec_TableVec'vec'u8'');

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$2_table_vec_TableVec'vec'u8'''(m: $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')), i: int) returns (e: $2_table_vec_TableVec'vec'u8'', m': $Mutation (Vec ($2_table_vec_TableVec'vec'u8'')))
{
    var len: int;
    var v: Vec ($2_table_vec_TableVec'vec'u8'');

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), e: $2_table_vec_TableVec'vec'u8'') returns (res: bool)  {
    res := $ContainsVec'$2_table_vec_TableVec'vec'u8'''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), e: $2_table_vec_TableVec'vec'u8'') returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$2_table_vec_TableVec'vec'u8'''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), n: int) returns (res: Vec ($2_table_vec_TableVec'vec'u8'')) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), n: int): Vec ($2_table_vec_TableVec'vec'u8'') {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), n: int) returns (res: Vec ($2_table_vec_TableVec'vec'u8'')) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'$2_table_vec_TableVec'vec'u8'''(v: Vec ($2_table_vec_TableVec'vec'u8''), n: int): Vec ($2_table_vec_TableVec'vec'u8'') {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$2_vec_map_Entry'$1_string_String_$1_string_String'`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(v1: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), v2: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), prefix: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), suffix: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), e: $2_vec_map_Entry'$1_string_String_$1_string_String'): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v, i), e))
}

function $IndexOfVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), e: $2_vec_map_Entry'$1_string_String_$1_string_String'): int;
axiom (forall v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), e: $2_vec_map_Entry'$1_string_String_$1_string_String':: {$IndexOfVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v, e)}
    (var i := $IndexOfVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v, e);
     if (!$ContainsVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(ReadVec(v, j), e))));


function {:inline} $RangeVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$2_vec_map_Entry'$1_string_String_$1_string_String''() returns (v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$2_vec_map_Entry'$1_string_String_$1_string_String''(): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), val: $2_vec_map_Entry'$1_string_String_$1_string_String') returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), val: $2_vec_map_Entry'$1_string_String_$1_string_String'): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) returns (e: $2_vec_map_Entry'$1_string_String_$1_string_String', m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), other: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), other: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), new_len: int) returns (v: (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), new_len: int) returns (v: (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), left: int, right: int) returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var left_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var mid_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var right_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), rot: int) returns (n: int, m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var len: int;
    var left_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var right_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var left_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var mid_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var right_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var mid_left_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var mid_right_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), i: int, e: $2_vec_map_Entry'$1_string_String_$1_string_String') returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))) {
    var left_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var right_vec: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), i: int) returns (dst: $2_vec_map_Entry'$1_string_String_$1_string_String') {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), i: int): $2_vec_map_Entry'$1_string_String_$1_string_String' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), index: int)
returns (dst: $Mutation ($2_vec_map_Entry'$1_string_String_$1_string_String'), m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')))
{
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), i: int): $2_vec_map_Entry'$1_string_String_$1_string_String' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), i: int, j: int) returns (m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')))
{
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), i: int, j: int): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), i: int) returns (e: $2_vec_map_Entry'$1_string_String_$1_string_String', m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')))
{
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$2_vec_map_Entry'$1_string_String_$1_string_String''(m: $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')), i: int) returns (e: $2_vec_map_Entry'$1_string_String_$1_string_String', m': $Mutation (Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')))
{
    var len: int;
    var v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), e: $2_vec_map_Entry'$1_string_String_$1_string_String') returns (res: bool)  {
    res := $ContainsVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), e: $2_vec_map_Entry'$1_string_String_$1_string_String') returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$2_vec_map_Entry'$1_string_String_$1_string_String''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), n: int) returns (res: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), n: int): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), n: int) returns (res: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'$2_vec_map_Entry'$1_string_String_$1_string_String''(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), n: int): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `vec'u8'`

// Not inlined. It appears faster this way.
function $IsEqual'vec'vec'u8'''(v1: Vec (Vec (int)), v2: Vec (Vec (int))): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'vec'u8''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'vec'u8'''(v: Vec (Vec (int)), prefix: Vec (Vec (int))): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'vec'u8''(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'vec'u8'''(v: Vec (Vec (int)), suffix: Vec (Vec (int))): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'vec'u8''(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'vec'u8'''(v: Vec (Vec (int))): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'vec'u8''(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'vec'u8'''(v: Vec (Vec (int))) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'vec'u8''(v: Vec (Vec (int)), e: Vec (int)): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'vec'u8''(ReadVec(v, i), e))
}

function $IndexOfVec'vec'u8''(v: Vec (Vec (int)), e: Vec (int)): int;
axiom (forall v: Vec (Vec (int)), e: Vec (int):: {$IndexOfVec'vec'u8''(v, e)}
    (var i := $IndexOfVec'vec'u8''(v, e);
     if (!$ContainsVec'vec'u8''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'vec'u8''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'vec'u8''(ReadVec(v, j), e))));


function {:inline} $RangeVec'vec'u8''(v: Vec (Vec (int))): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'vec'u8''(): Vec (Vec (int)) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'vec'u8''() returns (v: Vec (Vec (int))) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'vec'u8''(): Vec (Vec (int)) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'vec'u8''(v: Vec (Vec (int))) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'vec'u8''(m: $Mutation (Vec (Vec (int))), val: Vec (int)) returns (m': $Mutation (Vec (Vec (int)))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'vec'u8''(v: Vec (Vec (int)), val: Vec (int)): Vec (Vec (int)) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'vec'u8''(m: $Mutation (Vec (Vec (int)))) returns (e: Vec (int), m': $Mutation (Vec (Vec (int)))) {
    var v: Vec (Vec (int));
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'vec'u8''(m: $Mutation (Vec (Vec (int))), other: Vec (Vec (int))) returns (m': $Mutation (Vec (Vec (int)))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'vec'u8''(m: $Mutation (Vec (Vec (int)))) returns (m': $Mutation (Vec (Vec (int)))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'vec'u8''(m: $Mutation (Vec (Vec (int))), other: Vec (Vec (int))) returns (m': $Mutation (Vec (Vec (int)))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'vec'u8''(m: $Mutation (Vec (Vec (int))), new_len: int) returns (v: (Vec (Vec (int))), m': $Mutation (Vec (Vec (int)))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'vec'u8''(m: $Mutation (Vec (Vec (int))), new_len: int) returns (v: (Vec (Vec (int))), m': $Mutation (Vec (Vec (int)))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'vec'u8''(m: $Mutation (Vec (Vec (int))), left: int, right: int) returns (m': $Mutation (Vec (Vec (int)))) {
    var left_vec: Vec (Vec (int));
    var mid_vec: Vec (Vec (int));
    var right_vec: Vec (Vec (int));
    var v: Vec (Vec (int));
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'vec'u8''(m: $Mutation (Vec (Vec (int))), rot: int) returns (n: int, m': $Mutation (Vec (Vec (int)))) {
    var v: Vec (Vec (int));
    var len: int;
    var left_vec: Vec (Vec (int));
    var right_vec: Vec (Vec (int));
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'vec'u8''(m: $Mutation (Vec (Vec (int))), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (Vec (int)))) {
    var left_vec: Vec (Vec (int));
    var mid_vec: Vec (Vec (int));
    var right_vec: Vec (Vec (int));
    var mid_left_vec: Vec (Vec (int));
    var mid_right_vec: Vec (Vec (int));
    var v: Vec (Vec (int));
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'vec'u8''(m: $Mutation (Vec (Vec (int))), i: int, e: Vec (int)) returns (m': $Mutation (Vec (Vec (int)))) {
    var left_vec: Vec (Vec (int));
    var right_vec: Vec (Vec (int));
    var v: Vec (Vec (int));
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'vec'u8''(v: Vec (Vec (int))) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'vec'u8''(v: Vec (Vec (int))): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'vec'u8''(v: Vec (Vec (int)), i: int) returns (dst: Vec (int)) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'vec'u8''(v: Vec (Vec (int)), i: int): Vec (int) {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'vec'u8''(m: $Mutation (Vec (Vec (int))), index: int)
returns (dst: $Mutation (Vec (int)), m': $Mutation (Vec (Vec (int))))
{
    var v: Vec (Vec (int));
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'vec'u8''(v: Vec (Vec (int)), i: int): Vec (int) {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'vec'u8''(v: Vec (Vec (int))) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'vec'u8''(m: $Mutation (Vec (Vec (int))), i: int, j: int) returns (m': $Mutation (Vec (Vec (int))))
{
    var v: Vec (Vec (int));
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'vec'u8''(v: Vec (Vec (int)), i: int, j: int): Vec (Vec (int)) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'vec'u8''(m: $Mutation (Vec (Vec (int))), i: int) returns (e: Vec (int), m': $Mutation (Vec (Vec (int))))
{
    var v: Vec (Vec (int));

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'vec'u8''(m: $Mutation (Vec (Vec (int))), i: int) returns (e: Vec (int), m': $Mutation (Vec (Vec (int))))
{
    var len: int;
    var v: Vec (Vec (int));

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'vec'u8''(v: Vec (Vec (int)), e: Vec (int)) returns (res: bool)  {
    res := $ContainsVec'vec'u8''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'vec'u8''(v: Vec (Vec (int)), e: Vec (int)) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'vec'u8''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'vec'u8''(v: Vec (Vec (int)), n: int) returns (res: Vec (Vec (int))) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'vec'u8''(v: Vec (Vec (int)), n: int): Vec (Vec (int)) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'vec'u8''(v: Vec (Vec (int)), n: int) returns (res: Vec (Vec (int))) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'vec'u8''(v: Vec (Vec (int)), n: int): Vec (Vec (int)) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bool`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bool''(v1: Vec (bool), v2: Vec (bool)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bool'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bool''(v: Vec (bool), prefix: Vec (bool)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bool'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bool''(v: Vec (bool), suffix: Vec (bool)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bool'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bool''(v: Vec (bool)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bool'(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'bool''(v: Vec (bool)) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'bool'(v: Vec (bool), e: bool): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bool'(ReadVec(v, i), e))
}

function $IndexOfVec'bool'(v: Vec (bool), e: bool): int;
axiom (forall v: Vec (bool), e: bool:: {$IndexOfVec'bool'(v, e)}
    (var i := $IndexOfVec'bool'(v, e);
     if (!$ContainsVec'bool'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bool'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bool'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bool'(v: Vec (bool)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bool'(): Vec (bool) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bool'() returns (v: Vec (bool)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bool'(): Vec (bool) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bool'(v: Vec (bool)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bool'(m: $Mutation (Vec (bool)), val: bool) returns (m': $Mutation (Vec (bool))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bool'(v: Vec (bool), val: bool): Vec (bool) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bool'(m: $Mutation (Vec (bool))) returns (e: bool, m': $Mutation (Vec (bool))) {
    var v: Vec (bool);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bool'(m: $Mutation (Vec (bool)), other: Vec (bool)) returns (m': $Mutation (Vec (bool))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bool'(m: $Mutation (Vec (bool))) returns (m': $Mutation (Vec (bool))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bool'(m: $Mutation (Vec (bool)), other: Vec (bool)) returns (m': $Mutation (Vec (bool))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bool'(m: $Mutation (Vec (bool)), new_len: int) returns (v: (Vec (bool)), m': $Mutation (Vec (bool))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bool'(m: $Mutation (Vec (bool)), new_len: int) returns (v: (Vec (bool)), m': $Mutation (Vec (bool))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bool'(m: $Mutation (Vec (bool)), left: int, right: int) returns (m': $Mutation (Vec (bool))) {
    var left_vec: Vec (bool);
    var mid_vec: Vec (bool);
    var right_vec: Vec (bool);
    var v: Vec (bool);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bool'(m: $Mutation (Vec (bool)), rot: int) returns (n: int, m': $Mutation (Vec (bool))) {
    var v: Vec (bool);
    var len: int;
    var left_vec: Vec (bool);
    var right_vec: Vec (bool);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bool'(m: $Mutation (Vec (bool)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bool))) {
    var left_vec: Vec (bool);
    var mid_vec: Vec (bool);
    var right_vec: Vec (bool);
    var mid_left_vec: Vec (bool);
    var mid_right_vec: Vec (bool);
    var v: Vec (bool);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bool'(m: $Mutation (Vec (bool)), i: int, e: bool) returns (m': $Mutation (Vec (bool))) {
    var left_vec: Vec (bool);
    var right_vec: Vec (bool);
    var v: Vec (bool);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bool'(v: Vec (bool)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bool'(v: Vec (bool)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bool'(v: Vec (bool), i: int) returns (dst: bool) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bool'(v: Vec (bool), i: int): bool {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bool'(m: $Mutation (Vec (bool)), index: int)
returns (dst: $Mutation (bool), m': $Mutation (Vec (bool)))
{
    var v: Vec (bool);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bool'(v: Vec (bool), i: int): bool {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bool'(v: Vec (bool)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bool'(m: $Mutation (Vec (bool)), i: int, j: int) returns (m': $Mutation (Vec (bool)))
{
    var v: Vec (bool);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bool'(v: Vec (bool), i: int, j: int): Vec (bool) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bool'(m: $Mutation (Vec (bool)), i: int) returns (e: bool, m': $Mutation (Vec (bool)))
{
    var v: Vec (bool);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bool'(m: $Mutation (Vec (bool)), i: int) returns (e: bool, m': $Mutation (Vec (bool)))
{
    var len: int;
    var v: Vec (bool);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bool'(v: Vec (bool), e: bool) returns (res: bool)  {
    res := $ContainsVec'bool'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bool'(v: Vec (bool), e: bool) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bool'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'bool'(v: Vec (bool), n: int) returns (res: Vec (bool)) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'bool'(v: Vec (bool), n: int): Vec (bool) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'bool'(v: Vec (bool), n: int) returns (res: Vec (bool)) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'bool'(v: Vec (bool), n: int): Vec (bool) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u64''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u64''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u64'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u64''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u64'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u64''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u64'(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'u64''(v: Vec (int)) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'u64'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e))
}

function $IndexOfVec'u64'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u64'(v, e)}
    (var i := $IndexOfVec'u64'(v, e);
     if (!$ContainsVec'u64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u64'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u64'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u64'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u64'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u64'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u64'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u64'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u64'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u64'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u64'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u64'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u64'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u64'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u64'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u64'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u64'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u64'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u64'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u64'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u64'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u64'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u64'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u64'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'u64'(v: Vec (int), n: int) returns (res: Vec (int)) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'u64'(v: Vec (int), n: int): Vec (int) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'u64'(v: Vec (int), n: int) returns (res: Vec (int)) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'u64'(v: Vec (int), n: int): Vec (int) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'u8''(v: Vec (int)) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'u8'(v: Vec (int), n: int) returns (res: Vec (int)) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'u8'(v: Vec (int), n: int): Vec (int) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'u8'(v: Vec (int), n: int) returns (res: Vec (int)) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'u8'(v: Vec (int), n: int): Vec (int) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `vec'bv8'`

// Not inlined. It appears faster this way.
function $IsEqual'vec'vec'bv8'''(v1: Vec (Vec (bv8)), v2: Vec (Vec (bv8))): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'vec'bv8''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'vec'bv8'''(v: Vec (Vec (bv8)), prefix: Vec (Vec (bv8))): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'vec'bv8''(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'vec'bv8'''(v: Vec (Vec (bv8)), suffix: Vec (Vec (bv8))): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'vec'bv8''(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'vec'bv8'''(v: Vec (Vec (bv8))): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'vec'bv8''(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'vec'bv8'''(v: Vec (Vec (bv8))) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'vec'bv8''(v: Vec (Vec (bv8)), e: Vec (bv8)): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'vec'bv8''(ReadVec(v, i), e))
}

function $IndexOfVec'vec'bv8''(v: Vec (Vec (bv8)), e: Vec (bv8)): int;
axiom (forall v: Vec (Vec (bv8)), e: Vec (bv8):: {$IndexOfVec'vec'bv8''(v, e)}
    (var i := $IndexOfVec'vec'bv8''(v, e);
     if (!$ContainsVec'vec'bv8''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'vec'bv8''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'vec'bv8''(ReadVec(v, j), e))));


function {:inline} $RangeVec'vec'bv8''(v: Vec (Vec (bv8))): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'vec'bv8''(): Vec (Vec (bv8)) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'vec'bv8''() returns (v: Vec (Vec (bv8))) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'vec'bv8''(): Vec (Vec (bv8)) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'vec'bv8''(v: Vec (Vec (bv8))) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), val: Vec (bv8)) returns (m': $Mutation (Vec (Vec (bv8)))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'vec'bv8''(v: Vec (Vec (bv8)), val: Vec (bv8)): Vec (Vec (bv8)) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'vec'bv8''(m: $Mutation (Vec (Vec (bv8)))) returns (e: Vec (bv8), m': $Mutation (Vec (Vec (bv8)))) {
    var v: Vec (Vec (bv8));
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), other: Vec (Vec (bv8))) returns (m': $Mutation (Vec (Vec (bv8)))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'vec'bv8''(m: $Mutation (Vec (Vec (bv8)))) returns (m': $Mutation (Vec (Vec (bv8)))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), other: Vec (Vec (bv8))) returns (m': $Mutation (Vec (Vec (bv8)))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), new_len: int) returns (v: (Vec (Vec (bv8))), m': $Mutation (Vec (Vec (bv8)))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), new_len: int) returns (v: (Vec (Vec (bv8))), m': $Mutation (Vec (Vec (bv8)))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), left: int, right: int) returns (m': $Mutation (Vec (Vec (bv8)))) {
    var left_vec: Vec (Vec (bv8));
    var mid_vec: Vec (Vec (bv8));
    var right_vec: Vec (Vec (bv8));
    var v: Vec (Vec (bv8));
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), rot: int) returns (n: int, m': $Mutation (Vec (Vec (bv8)))) {
    var v: Vec (Vec (bv8));
    var len: int;
    var left_vec: Vec (Vec (bv8));
    var right_vec: Vec (Vec (bv8));
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (Vec (bv8)))) {
    var left_vec: Vec (Vec (bv8));
    var mid_vec: Vec (Vec (bv8));
    var right_vec: Vec (Vec (bv8));
    var mid_left_vec: Vec (Vec (bv8));
    var mid_right_vec: Vec (Vec (bv8));
    var v: Vec (Vec (bv8));
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), i: int, e: Vec (bv8)) returns (m': $Mutation (Vec (Vec (bv8)))) {
    var left_vec: Vec (Vec (bv8));
    var right_vec: Vec (Vec (bv8));
    var v: Vec (Vec (bv8));
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'vec'bv8''(v: Vec (Vec (bv8))) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'vec'bv8''(v: Vec (Vec (bv8))): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'vec'bv8''(v: Vec (Vec (bv8)), i: int) returns (dst: Vec (bv8)) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'vec'bv8''(v: Vec (Vec (bv8)), i: int): Vec (bv8) {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), index: int)
returns (dst: $Mutation (Vec (bv8)), m': $Mutation (Vec (Vec (bv8))))
{
    var v: Vec (Vec (bv8));
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'vec'bv8''(v: Vec (Vec (bv8)), i: int): Vec (bv8) {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'vec'bv8''(v: Vec (Vec (bv8))) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), i: int, j: int) returns (m': $Mutation (Vec (Vec (bv8))))
{
    var v: Vec (Vec (bv8));
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'vec'bv8''(v: Vec (Vec (bv8)), i: int, j: int): Vec (Vec (bv8)) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), i: int) returns (e: Vec (bv8), m': $Mutation (Vec (Vec (bv8))))
{
    var v: Vec (Vec (bv8));

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'vec'bv8''(m: $Mutation (Vec (Vec (bv8))), i: int) returns (e: Vec (bv8), m': $Mutation (Vec (Vec (bv8))))
{
    var len: int;
    var v: Vec (Vec (bv8));

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'vec'bv8''(v: Vec (Vec (bv8)), e: Vec (bv8)) returns (res: bool)  {
    res := $ContainsVec'vec'bv8''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'vec'bv8''(v: Vec (Vec (bv8)), e: Vec (bv8)) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'vec'bv8''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'vec'bv8''(v: Vec (Vec (bv8)), n: int) returns (res: Vec (Vec (bv8))) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'vec'bv8''(v: Vec (Vec (bv8)), n: int): Vec (Vec (bv8)) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'vec'bv8''(v: Vec (Vec (bv8)), n: int) returns (res: Vec (Vec (bv8))) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'vec'bv8''(v: Vec (Vec (bv8)), n: int): Vec (Vec (bv8)) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv64''(v1: Vec (bv64), v2: Vec (bv64)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv64''(v: Vec (bv64), prefix: Vec (bv64)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv64'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv64''(v: Vec (bv64), suffix: Vec (bv64)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv64'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv64''(v: Vec (bv64)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv64'(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'bv64''(v: Vec (bv64)) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'bv64'(v: Vec (bv64), e: bv64): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv64'(ReadVec(v, i), e))
}

function $IndexOfVec'bv64'(v: Vec (bv64), e: bv64): int;
axiom (forall v: Vec (bv64), e: bv64:: {$IndexOfVec'bv64'(v, e)}
    (var i := $IndexOfVec'bv64'(v, e);
     if (!$ContainsVec'bv64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv64'(v: Vec (bv64)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv64'(): Vec (bv64) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv64'() returns (v: Vec (bv64)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv64'(): Vec (bv64) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv64'(v: Vec (bv64)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv64'(m: $Mutation (Vec (bv64)), val: bv64) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv64'(v: Vec (bv64), val: bv64): Vec (bv64) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv64'(m: $Mutation (Vec (bv64))) returns (e: bv64, m': $Mutation (Vec (bv64))) {
    var v: Vec (bv64);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv64'(m: $Mutation (Vec (bv64)), other: Vec (bv64)) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv64'(m: $Mutation (Vec (bv64))) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv64'(m: $Mutation (Vec (bv64)), other: Vec (bv64)) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv64'(m: $Mutation (Vec (bv64)), new_len: int) returns (v: (Vec (bv64)), m': $Mutation (Vec (bv64))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv64'(m: $Mutation (Vec (bv64)), new_len: int) returns (v: (Vec (bv64)), m': $Mutation (Vec (bv64))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv64'(m: $Mutation (Vec (bv64)), left: int, right: int) returns (m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var mid_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var v: Vec (bv64);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv64'(m: $Mutation (Vec (bv64)), rot: int) returns (n: int, m': $Mutation (Vec (bv64))) {
    var v: Vec (bv64);
    var len: int;
    var left_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv64'(m: $Mutation (Vec (bv64)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var mid_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var mid_left_vec: Vec (bv64);
    var mid_right_vec: Vec (bv64);
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv64'(m: $Mutation (Vec (bv64)), i: int, e: bv64) returns (m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv64'(v: Vec (bv64)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv64'(v: Vec (bv64)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv64'(v: Vec (bv64), i: int) returns (dst: bv64) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv64'(v: Vec (bv64), i: int): bv64 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv64'(m: $Mutation (Vec (bv64)), index: int)
returns (dst: $Mutation (bv64), m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv64'(v: Vec (bv64), i: int): bv64 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv64'(v: Vec (bv64)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv64'(m: $Mutation (Vec (bv64)), i: int, j: int) returns (m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv64'(v: Vec (bv64), i: int, j: int): Vec (bv64) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv64'(m: $Mutation (Vec (bv64)), i: int) returns (e: bv64, m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv64'(m: $Mutation (Vec (bv64)), i: int) returns (e: bv64, m': $Mutation (Vec (bv64)))
{
    var len: int;
    var v: Vec (bv64);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv64'(v: Vec (bv64), e: bv64) returns (res: bool)  {
    res := $ContainsVec'bv64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv64'(v: Vec (bv64), e: bv64) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv64'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'bv64'(v: Vec (bv64), n: int) returns (res: Vec (bv64)) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'bv64'(v: Vec (bv64), n: int): Vec (bv64) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'bv64'(v: Vec (bv64), n: int) returns (res: Vec (bv64)) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'bv64'(v: Vec (bv64), n: int): Vec (bv64) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv8''(v1: Vec (bv8), v2: Vec (bv8)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv8''(v: Vec (bv8), prefix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv8''(v: Vec (bv8), suffix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv8''(v: Vec (bv8)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv8'(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec'bv8''(v: Vec (bv8)) returns (res: bool) {
    res := true;
}


function {:inline} $ContainsVec'bv8'(v: Vec (bv8), e: bv8): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e))
}

function $IndexOfVec'bv8'(v: Vec (bv8), e: bv8): int;
axiom (forall v: Vec (bv8), e: bv8:: {$IndexOfVec'bv8'(v, e)}
    (var i := $IndexOfVec'bv8'(v, e);
     if (!$ContainsVec'bv8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv8'(v: Vec (bv8)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv8'() returns (v: Vec (bv8)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv8'(v: Vec (bv8)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv8'(m: $Mutation (Vec (bv8)), val: bv8) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv8'(v: Vec (bv8), val: bv8): Vec (bv8) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv8'(m: $Mutation (Vec (bv8))) returns (e: bv8, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv8'(m: $Mutation (Vec (bv8))) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, right: int) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv8'(m: $Mutation (Vec (bv8)), rot: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var mid_left_vec: Vec (bv8);
    var mid_right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv8'(m: $Mutation (Vec (bv8)), i: int, e: bv8) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv8'(v: Vec (bv8)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv8'(v: Vec (bv8)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv8'(v: Vec (bv8), i: int) returns (dst: bv8) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv8'(m: $Mutation (Vec (bv8)), index: int)
returns (dst: $Mutation (bv8), m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv8'(v: Vec (bv8)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv8'(m: $Mutation (Vec (bv8)), i: int, j: int) returns (m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv8'(v: Vec (bv8), i: int, j: int): Vec (bv8) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv8'(v: Vec (bv8), e: bv8) returns (res: bool)  {
    res := $ContainsVec'bv8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv8'(v: Vec (bv8), e: bv8) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take'bv8'(v: Vec (bv8), n: int) returns (res: Vec (bv8)) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take'bv8'(v: Vec (bv8), n: int): Vec (bv8) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip'bv8'(v: Vec (bv8), n: int) returns (res: Vec (bv8)) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip'bv8'(v: Vec (bv8), n: int): Vec (bv8) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}


// ==================================================================================
// Native VecSet

// ==================================================================================
// Native TableVec

// ==================================================================================
// Native VecMap

// ----------------------------------------------------------------------------------
// Native VecMap implementation for key type `$1_string_String` and value type `$1_string_String`

function {:inline} $ContainsVecMap'$1_string_String_$1_string_String'(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), k: $1_string_String): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_string_String'(ReadVec(v, i)->$key, k))
}

function $IndexOfVecMap'$1_string_String_$1_string_String'(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), k: $1_string_String): int;
axiom (forall v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'), k: $1_string_String :: {$IndexOfVecMap'$1_string_String_$1_string_String'(v, k)}
    (var i := $IndexOfVecMap'$1_string_String_$1_string_String'(v, k);
     if (!$ContainsVecMap'$1_string_String_$1_string_String'(v, k)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_string_String'(ReadVec(v, i)->$key, k) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_string_String'(ReadVec(v, i)->$key, k))));

procedure {:inline 1} $2_vec_map_get_idx_opt'$1_string_String_$1_string_String'(
    m: $2_vec_map_VecMap'$1_string_String_$1_string_String',
    k: $1_string_String
) returns (res: $1_option_Option'u64') {
    var res0: int;
    res0 := $IndexOfVecMap'$1_string_String_$1_string_String'(m->$contents, k);
    if (res0 >= 0) {
        res := $1_option_Option'u64'(MakeVec1(res0));
    } else {
        res := $1_option_Option'u64'(EmptyVec());
    }
}

function $VecMapKeys'$1_string_String_$1_string_String'(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): Vec ($1_string_String);
axiom (forall v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') :: {$VecMapKeys'$1_string_String_$1_string_String'(v)}
    (var keys := $VecMapKeys'$1_string_String_$1_string_String'(v);
     LenVec(keys) == LenVec(v) &&
     (forall i: int :: InRangeVec(v, i) ==> $IsEqual'$1_string_String'(ReadVec(keys, i), ReadVec(v, i)->$key))));

function $VecMapValues'$1_string_String_$1_string_String'(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): Vec ($1_string_String);
axiom (forall v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String') :: {$VecMapValues'$1_string_String_$1_string_String'(v)}
    (var values := $VecMapValues'$1_string_String_$1_string_String'(v);
     LenVec(values) == LenVec(v) &&
     (forall i: int :: InRangeVec(v, i) ==> $IsEqual'$1_string_String'(ReadVec(values, i), ReadVec(v, i)->$value))));

procedure {:inline 1} $2_vec_map_keys'$1_string_String_$1_string_String'(m: $2_vec_map_VecMap'$1_string_String_$1_string_String') returns (res: Vec ($1_string_String)) {
    res := $VecMapKeys'$1_string_String_$1_string_String'(m->$contents);
}

procedure {:inline 1} $2_vec_map_into_keys_values'$1_string_String_$1_string_String'(m: $2_vec_map_VecMap'$1_string_String_$1_string_String') returns (res0: Vec ($1_string_String), res1: Vec ($1_string_String)) {
    res0 := $VecMapKeys'$1_string_String_$1_string_String'(m->$contents);
    res1 := $VecMapValues'$1_string_String_$1_string_String'(m->$contents);
}

function $DisjointVecMap'$1_string_String_$1_string_String'(v: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): bool {
    (forall i: int, j: int :: {$IsEqual'$1_string_String'(ReadVec(v, i)->$key, ReadVec(v, j)->$key)}
        InRangeVec(v, i) && InRangeVec(v, j) && i != j ==> !$IsEqual'$1_string_String'(ReadVec(v, i)->$key, ReadVec(v, j)->$key))
}

function $VecMapFromKeysValues'$1_string_String_$1_string_String'(keys: Vec ($1_string_String), values: Vec ($1_string_String)): Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
axiom (forall keys: Vec ($1_string_String), values: Vec ($1_string_String) :: {$VecMapFromKeysValues'$1_string_String_$1_string_String'(keys, values)}
    (var entries := $VecMapFromKeysValues'$1_string_String_$1_string_String'(keys, values);
     LenVec(entries) == LenVec(keys) &&
     (forall i: int :: InRangeVec(keys, i) ==>
        $IsEqual'$1_string_String'(ReadVec(entries, i)->$key, ReadVec(keys, i)) && $IsEqual'$1_string_String'(ReadVec(entries, i)->$value, ReadVec(values, i)))));

procedure {:inline 1} $2_vec_map_from_keys_values'$1_string_String_$1_string_String'(keys: Vec ($1_string_String), values: Vec ($1_string_String)) returns (res: $2_vec_map_VecMap'$1_string_String_$1_string_String') {
    var entries: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String');
    if (LenVec(keys) != LenVec(values)) {
        call $Abort(5);
        return;
    }
    entries := $VecMapFromKeysValues'$1_string_String_$1_string_String'(keys, values);
    if (!$DisjointVecMap'$1_string_String_$1_string_String'(entries)) {
        call $Abort(0);
        return;
    }
    res := $2_vec_map_VecMap'$1_string_String_$1_string_String'(entries);
}



// ==================================================================================
// Native Table

// ----------------------------------------------------------------------------------
// Native Table key encoding for type `u64`

function $EncodeKey'u64'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'u64'(k1), $EncodeKey'u64'(k2)}
    $IsEqual'u64'(k1, k2) <==> $EncodeKey'u64'(k1) == $EncodeKey'u64'(k2)
);


// ----------------------------------------------------------------------------------
// Native TableArray IsValid and IsEqual implementation for type `vec'u8'`

function $IsEqual''Table'int_vec'u8''''(t1: Table int (Vec (int)), t2: Table int (Vec (int))): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> $IsEqual'vec'u8''(GetTable(t1, k), GetTable(t2, k))) &&
    (forall k: int :: ContainsTable(t2, k) ==> $IsEqual'vec'u8''(GetTable(t1, k), GetTable(t2, k)))
}

// Not inlined.
function $IsValid''Table'int_vec'u8''''(t: Table int (Vec (int))): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'vec'u8''(GetTable(t, i)))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(u64,vec'u8')`

datatype $2_table_Table'u64_vec'u8'' {
    $2_table_Table'u64_vec'u8''($id: $2_object_UID, $contents: Table int (Vec (int)))
}

function {:inline} $Update'$2_table_Table'u64_vec'u8'''_id(s: $2_table_Table'u64_vec'u8'', x: $2_object_UID): $2_table_Table'u64_vec'u8'' {
    $2_table_Table'u64_vec'u8''(x, s->$contents)
}
function {:inline} $Update'$2_table_Table'u64_vec'u8'''_contents(s: $2_table_Table'u64_vec'u8'', x: Table int (Vec (int))): $2_table_Table'u64_vec'u8'' {
    $2_table_Table'u64_vec'u8''(s->$id, x)
}function $IsEqual'$2_table_Table'u64_vec'u8'''(t1: $2_table_Table'u64_vec'u8'', t2: $2_table_Table'u64_vec'u8''): bool {
    // TODO use $IsEqual'Table int (Vec (int))'(t1->$contents, t2->$contents)
    LenTable(t1->$contents) == LenTable(t2->$contents) &&
    (forall k: int :: ContainsTable(t1->$contents, k) <==> ContainsTable(t2->$contents, k)) &&
    (forall k: int :: ContainsTable(t1->$contents, k) ==> $IsEqual'vec'u8''(GetTable(t1->$contents, k), GetTable(t2->$contents, k))) &&
    (forall k: int :: ContainsTable(t2->$contents, k) ==> $IsEqual'vec'u8''(GetTable(t1->$contents, k), GetTable(t2->$contents, k)))
}

// Not inlined.
function $IsValid'$2_table_Table'u64_vec'u8'''(t: $2_table_Table'u64_vec'u8''): bool {
    // TODO use $IsValid'Table int (Vec (int))'(t->$contents)
    $IsValid'u64'(LenTable(t->$contents)) &&
    (forall i: int:: ContainsTable(t->$contents, i) ==> $IsValid'vec'u8''(GetTable(t->$contents, i)))
}
procedure {:inline 2} $2_table_add'u64_vec'u8''(m: $Mutation ($2_table_Table'u64_vec'u8''), k: int, v: Vec (int)) returns (m': $Mutation($2_table_Table'u64_vec'u8'')) {
    var enc_k: int;
    var t: $2_table_Table'u64_vec'u8'';
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, $Update'$2_table_Table'u64_vec'u8'''_contents(t, AddTable(t->$contents, enc_k, v)));
    }
}
procedure {:inline 2} $2_table_borrow'u64_vec'u8''(t: $2_table_Table'u64_vec'u8'', k: int) returns (v: Vec (int)) {
    var enc_k: int;
    enc_k := $EncodeKey'u64'(k);
    if (!ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$contents, $EncodeKey'u64'(k));
    }
}
procedure {:inline 2} $2_table_borrow_mut'u64_vec'u8''(m: $Mutation ($2_table_Table'u64_vec'u8''), k: int)
returns (dst: $Mutation (Vec (int)), m': $Mutation ($2_table_Table'u64_vec'u8'')) {
    var enc_k: int;
    var t: $2_table_Table'u64_vec'u8'';
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(ExtendVec(m->p, 1), enc_k), GetTable(t->$contents, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $2_table_remove'u64_vec'u8''(m: $Mutation ($2_table_Table'u64_vec'u8''), k: int)
returns (v: Vec (int), m': $Mutation($2_table_Table'u64_vec'u8'')) {
    var enc_k: int;
    var t: $2_table_Table'u64_vec'u8'';
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$contents, enc_k);
        m' := $UpdateMutation(m, $Update'$2_table_Table'u64_vec'u8'''_contents(t, RemoveTable(t->$contents, enc_k)));
    }
}
procedure {:inline 2} $2_table_contains'u64_vec'u8''(t: ($2_table_Table'u64_vec'u8''), k: int) returns (r: bool) {
    r := ContainsTable(t->$contents, $EncodeKey'u64'(k));
}
procedure {:inline 2} $2_table_length'u64_vec'u8''(t: ($2_table_Table'u64_vec'u8'')) returns (l: int) {
    l := LenTable(t->$contents);
}
procedure {:inline 2} $2_table_is_empty'u64_vec'u8''(t: ($2_table_Table'u64_vec'u8'')) returns (r: bool) {
    r := LenTable(t->$contents) == 0;
}
procedure {:inline 2} $2_table_destroy_empty'u64_vec'u8''(t: $2_table_Table'u64_vec'u8'') {
    if (LenTable(t->$contents) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}



// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int)
}
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'(s->$addr)
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamBool ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> t is $TypeParamBool);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU8 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> t is $TypeParamU8);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU16 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> t is $TypeParamU16);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU32 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> t is $TypeParamU32);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU64 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> t is $TypeParamU64);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU128 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> t is $TypeParamU128);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU256 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> t is $TypeParamU256);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamAddress ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> t is $TypeParamAddress);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamSigner ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> t is $TypeParamSigner);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamVector ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(t->e)), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> t is $TypeParamVector);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamStruct ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(t->a)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->m), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->s)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> t is $TypeParamVector);


// Given Types for Type Parameters

datatype #0 {
    #0($id: $2_object_UID)
}
procedure {:inline 1} $2_object_borrow_uid'#0'(obj: #0) returns (res: $2_object_UID) {
    res := obj->$id;
}
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
procedure {:inline 1} $0_prover_type_inv'#0'(x: #0) returns (res: bool) { res := true; }
var #0_info: $TypeParamInfo;
datatype #1 {
    #1($id: $2_object_UID)
}
procedure {:inline 1} $2_object_borrow_uid'#1'(obj: #1) returns (res: $2_object_UID) {
    res := obj->$id;
}
function {:inline} $IsEqual'#1'(x1: #1, x2: #1): bool { x1 == x2 }
function {:inline} $IsValid'#1'(x: #1): bool { true }
procedure {:inline 1} $0_prover_type_inv'#1'(x: #1) returns (res: bool) { res := true; }
var #1_info: $TypeParamInfo;

var $global_var__'#0_#1' : #1 where $IsValid'#1'($global_var__'#0_#1');
// fun ghost::havoc_global<#0, #1> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/ghost.move:29:1+32
procedure {:inline 1} $0_ghost_havoc_global'#0_#1'() returns ()
{
    havoc $global_var__'#0_#1';
}

// struct option::Option<bool> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/move-stdlib/sources/option.move:9:1+81
datatype $1_option_Option'bool' {
    $1_option_Option'bool'($vec: Vec (bool))
}
function {:inline} $Update'$1_option_Option'bool''_vec(s: $1_option_Option'bool', x: Vec (bool)): $1_option_Option'bool' {
    $1_option_Option'bool'(x)
}
function {:inline} $IsEqual'$1_option_Option'bool''(s1: $1_option_Option'bool', s2: $1_option_Option'bool'): bool {
    $IsEqual'vec'bool''(s1->$vec, s2->$vec)}
procedure {:inline 1} $0_prover_type_inv'$1_option_Option'bool''(s: $1_option_Option'bool') returns (res: bool) {
    res := true;
    return;
}

// struct option::Option<u64> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/move-stdlib/sources/option.move:9:1+81
datatype $1_option_Option'u64' {
    $1_option_Option'u64'($vec: Vec (int))
}
function {:inline} $Update'$1_option_Option'u64''_vec(s: $1_option_Option'u64', x: Vec (int)): $1_option_Option'u64' {
    $1_option_Option'u64'(x)
}
function {:inline} $IsEqual'$1_option_Option'u64''(s1: $1_option_Option'u64', s2: $1_option_Option'u64'): bool {
    $IsEqual'vec'u64''(s1->$vec, s2->$vec)}
procedure {:inline 1} $0_prover_type_inv'$1_option_Option'u64''(s: $1_option_Option'u64') returns (res: bool) {
    res := true;
    return;
}

// struct option::Option<vector<u8>> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/move-stdlib/sources/option.move:9:1+81
datatype $1_option_Option'vec'u8'' {
    $1_option_Option'vec'u8''($vec: Vec (Vec (int)))
}
function {:inline} $Update'$1_option_Option'vec'u8'''_vec(s: $1_option_Option'vec'u8'', x: Vec (Vec (int))): $1_option_Option'vec'u8'' {
    $1_option_Option'vec'u8''(x)
}
function {:inline} $IsEqual'$1_option_Option'vec'u8'''(s1: $1_option_Option'vec'u8'', s2: $1_option_Option'vec'u8''): bool {
    $IsEqual'vec'vec'u8'''(s1->$vec, s2->$vec)}
procedure {:inline 1} $0_prover_type_inv'$1_option_Option'vec'u8'''(s: $1_option_Option'vec'u8'') returns (res: bool) {
    res := true;
    return;
}

// struct option::Option<string::String> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/move-stdlib/sources/option.move:9:1+81
datatype $1_option_Option'$1_string_String' {
    $1_option_Option'$1_string_String'($vec: Vec ($1_string_String))
}
function {:inline} $Update'$1_option_Option'$1_string_String''_vec(s: $1_option_Option'$1_string_String', x: Vec ($1_string_String)): $1_option_Option'$1_string_String' {
    $1_option_Option'$1_string_String'(x)
}
function {:inline} $IsEqual'$1_option_Option'$1_string_String''(s1: $1_option_Option'$1_string_String', s2: $1_option_Option'$1_string_String'): bool {
    $IsEqual'vec'$1_string_String''(s1->$vec, s2->$vec)}
procedure {:inline 1} $0_prover_type_inv'$1_option_Option'$1_string_String''(s: $1_option_Option'$1_string_String') returns (res: bool) {
    res := true;
    return;
}

// struct option::Option<table_vec::TableVec<vector<u8>>> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/move-stdlib/sources/option.move:9:1+81
datatype $1_option_Option'$2_table_vec_TableVec'vec'u8''' {
    $1_option_Option'$2_table_vec_TableVec'vec'u8'''($vec: Vec ($2_table_vec_TableVec'vec'u8''))
}
function {:inline} $Update'$1_option_Option'$2_table_vec_TableVec'vec'u8''''_vec(s: $1_option_Option'$2_table_vec_TableVec'vec'u8''', x: Vec ($2_table_vec_TableVec'vec'u8'')): $1_option_Option'$2_table_vec_TableVec'vec'u8''' {
    $1_option_Option'$2_table_vec_TableVec'vec'u8'''(x)
}
function {:inline} $IsEqual'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s1: $1_option_Option'$2_table_vec_TableVec'vec'u8''', s2: $1_option_Option'$2_table_vec_TableVec'vec'u8'''): bool {
    $IsEqual'vec'$2_table_vec_TableVec'vec'u8''''(s1->$vec, s2->$vec)}
procedure {:inline 1} $0_prover_type_inv'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s: $1_option_Option'$2_table_vec_TableVec'vec'u8''') returns (res: bool) {
    res := true;
    return;
}

// struct tx_context::TxContext at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:18:1+474
datatype $2_tx_context_TxContext {
    $2_tx_context_TxContext($sender: int, $tx_hash: Vec (int), $epoch: int, $epoch_timestamp_ms: int, $ids_created: int)
}
function {:inline} $Update'$2_tx_context_TxContext'_sender(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext(x, s->$tx_hash, s->$epoch, s->$epoch_timestamp_ms, s->$ids_created)
}
function {:inline} $Update'$2_tx_context_TxContext'_tx_hash(s: $2_tx_context_TxContext, x: Vec (int)): $2_tx_context_TxContext {
    $2_tx_context_TxContext(s->$sender, x, s->$epoch, s->$epoch_timestamp_ms, s->$ids_created)
}
function {:inline} $Update'$2_tx_context_TxContext'_epoch(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext(s->$sender, s->$tx_hash, x, s->$epoch_timestamp_ms, s->$ids_created)
}
function {:inline} $Update'$2_tx_context_TxContext'_epoch_timestamp_ms(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext(s->$sender, s->$tx_hash, s->$epoch, x, s->$ids_created)
}
function {:inline} $Update'$2_tx_context_TxContext'_ids_created(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext(s->$sender, s->$tx_hash, s->$epoch, s->$epoch_timestamp_ms, x)
}
function $IsValid'$2_tx_context_TxContext'(s: $2_tx_context_TxContext): bool {
    $IsValid'address'(s->$sender)
      && $IsValid'vec'u8''(s->$tx_hash)
      && $IsValid'u64'(s->$epoch)
      && $IsValid'u64'(s->$epoch_timestamp_ms)
      && $IsValid'u64'(s->$ids_created)
}
function {:inline} $IsEqual'$2_tx_context_TxContext'(s1: $2_tx_context_TxContext, s2: $2_tx_context_TxContext): bool {
    $IsEqual'address'(s1->$sender, s2->$sender)
    && $IsEqual'vec'u8''(s1->$tx_hash, s2->$tx_hash)
    && $IsEqual'u64'(s1->$epoch, s2->$epoch)
    && $IsEqual'u64'(s1->$epoch_timestamp_ms, s2->$epoch_timestamp_ms)
    && $IsEqual'u64'(s1->$ids_created, s2->$ids_created)}
procedure {:inline 1} $0_prover_type_inv'$2_tx_context_TxContext'(s: $2_tx_context_TxContext) returns (res: bool) {
    res := true;
    return;
}

// fun tx_context::digest [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:41:1+70
procedure {:inline 1} $2_tx_context_digest(_$t0: $2_tx_context_TxContext) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:41:1+1
    assume {:print "$at(134,1361,1362)"} true;
    assume {:print "$track_local(71,2,0,$2_tx_context_TxContext):", $t0} $t0 == $t0;

    // $t1 := get_field<tx_context::TxContext>.tx_hash($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:42:5+13
    assume {:print "$at(134,1416,1429)"} true;
    $t1 := $t0->$tx_hash;

    // trace_return[0]($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:42:5+13
    assume {:print "$track_return(71,2,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:43:1+1
    assume {:print "$at(134,1430,1431)"} true;
L1:

    // return $t1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/tx_context.move:43:1+1
    assume {:print "$at(134,1430,1431)"} true;
    $ret0 := $t1;
    return;

}

// struct vec_map::Entry<string::String, string::String> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/vec_map.move:35:1+83
datatype $2_vec_map_Entry'$1_string_String_$1_string_String' {
    $2_vec_map_Entry'$1_string_String_$1_string_String'($key: $1_string_String, $value: $1_string_String)
}
function {:inline} $Update'$2_vec_map_Entry'$1_string_String_$1_string_String''_key(s: $2_vec_map_Entry'$1_string_String_$1_string_String', x: $1_string_String): $2_vec_map_Entry'$1_string_String_$1_string_String' {
    $2_vec_map_Entry'$1_string_String_$1_string_String'(x, s->$value)
}
function {:inline} $Update'$2_vec_map_Entry'$1_string_String_$1_string_String''_value(s: $2_vec_map_Entry'$1_string_String_$1_string_String', x: $1_string_String): $2_vec_map_Entry'$1_string_String_$1_string_String' {
    $2_vec_map_Entry'$1_string_String_$1_string_String'(s->$key, x)
}
function $IsValid'$2_vec_map_Entry'$1_string_String_$1_string_String''(s: $2_vec_map_Entry'$1_string_String_$1_string_String'): bool {
    $IsValid'$1_string_String'(s->$key)
      && $IsValid'$1_string_String'(s->$value)
}
function {:inline} $IsEqual'$2_vec_map_Entry'$1_string_String_$1_string_String''(s1: $2_vec_map_Entry'$1_string_String_$1_string_String', s2: $2_vec_map_Entry'$1_string_String_$1_string_String'): bool {
    $IsEqual'$1_string_String'(s1->$key, s2->$key)
    && $IsEqual'$1_string_String'(s1->$value, s2->$value)}
procedure {:inline 1} $0_prover_type_inv'$2_vec_map_Entry'$1_string_String_$1_string_String''(s: $2_vec_map_Entry'$1_string_String_$1_string_String') returns (res: bool) {
    res := true;
    return;
}

// struct vec_map::VecMap<string::String, string::String> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/vec_map.move:30:1+93
datatype $2_vec_map_VecMap'$1_string_String_$1_string_String' {
    $2_vec_map_VecMap'$1_string_String_$1_string_String'($contents: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String'))
}
function {:inline} $Update'$2_vec_map_VecMap'$1_string_String_$1_string_String''_contents(s: $2_vec_map_VecMap'$1_string_String_$1_string_String', x: Vec ($2_vec_map_Entry'$1_string_String_$1_string_String')): $2_vec_map_VecMap'$1_string_String_$1_string_String' {
    $2_vec_map_VecMap'$1_string_String_$1_string_String'(x)
}
function $IsValid'$2_vec_map_VecMap'$1_string_String_$1_string_String''(s: $2_vec_map_VecMap'$1_string_String_$1_string_String'): bool {
    $IsValid'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(s->$contents)
      && $DisjointVecMap'$1_string_String_$1_string_String'(s->$contents)
}
function {:inline} $IsEqual'$2_vec_map_VecMap'$1_string_String_$1_string_String''(s1: $2_vec_map_VecMap'$1_string_String_$1_string_String', s2: $2_vec_map_VecMap'$1_string_String_$1_string_String'): bool {
    $IsEqual'vec'$2_vec_map_Entry'$1_string_String_$1_string_String'''(s1->$contents, s2->$contents)}
procedure {:inline 1} $0_prover_type_inv'$2_vec_map_VecMap'$1_string_String_$1_string_String''(s: $2_vec_map_VecMap'$1_string_String_$1_string_String') returns (res: bool) {
    res := true;
    return;
}

// struct string::String at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/move-stdlib/sources/string.move:18:1+69
datatype $1_string_String {
    $1_string_String($bytes: Vec (int))
}
function {:inline} $Update'$1_string_String'_bytes(s: $1_string_String, x: Vec (int)): $1_string_String {
    $1_string_String(x)
}
function $IsValid'$1_string_String'(s: $1_string_String): bool {
    $IsValid'vec'u8''(s->$bytes)
}
function {:inline} $IsEqual'$1_string_String'(s1: $1_string_String, s2: $1_string_String): bool {
    $IsEqual'vec'u8''(s1->$bytes, s2->$bytes)}
procedure {:inline 1} $0_prover_type_inv'$1_string_String'(s: $1_string_String) returns (res: bool) {
    res := true;
    return;
}

// struct object::ID at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:58:1+390
datatype $2_object_ID {
    $2_object_ID($bytes: int)
}
function {:inline} $Update'$2_object_ID'_bytes(s: $2_object_ID, x: int): $2_object_ID {
    $2_object_ID(x)
}
function $IsValid'$2_object_ID'(s: $2_object_ID): bool {
    $IsValid'address'(s->$bytes)
}
function {:inline} $IsEqual'$2_object_ID'(s1: $2_object_ID, s2: $2_object_ID): bool {
    s1 == s2
}
procedure {:inline 1} $0_prover_type_inv'$2_object_ID'(s: $2_object_ID) returns (res: bool) {
    res := true;
    return;
}

// struct object::UID at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:72:1+43
datatype $2_object_UID {
    $2_object_UID($id: $2_object_ID)
}
function {:inline} $Update'$2_object_UID'_id(s: $2_object_UID, x: $2_object_ID): $2_object_UID {
    $2_object_UID(x)
}
function $IsValid'$2_object_UID'(s: $2_object_UID): bool {
    $IsValid'$2_object_ID'(s->$id)
}
function {:inline} $IsEqual'$2_object_UID'(s1: $2_object_UID, s2: $2_object_UID): bool {
    s1 == s2
}
procedure {:inline 1} $0_prover_type_inv'$2_object_UID'(s: $2_object_UID) returns (res: bool) {
    res := true;
    return;
}

// fun object::new [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:185:1+114
procedure {:inline 1} $2_object_new(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_object_UID, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: $2_object_ID;
    var $t4: $2_object_UID;
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_object_UID': $2_object_UID;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:185:1+1
    assume {:print "$at(118,5754,5755)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(78,16,0,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t1 := tx_context::fresh_object_address($t0) on_abort goto L2 with $t2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:187:25+26
    assume {:print "$at(118,5831,5857)"} true;
    call $t1,$t0 := $2_tx_context_fresh_object_address($t0);
    if ($abort_flag) {
        assume {:print "$at(118,5831,5857)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(78,16):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := pack object::ID($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:187:13+40
    $t3 := $2_object_ID($t1);

    // $t4 := pack object::UID($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:186:5+65
    assume {:print "$at(118,5801,5866)"} true;
    $t4 := $2_object_UID($t3);

    // trace_return[0]($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:186:5+65
    assume {:print "$track_return(78,16,0,$2_object_UID):", $t4} $t4 == $t4;

    // trace_local[ctx]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:186:5+65
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(78,16,0,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:189:1+1
    assume {:print "$at(118,5867,5868)"} true;
L1:

    // return $t4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:189:1+1
    assume {:print "$at(118,5867,5868)"} true;
    $ret0 := $t4;
    $ret1 := $t0;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:189:1+1
L2:

    // abort($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:189:1+1
    assume {:print "$at(118,5867,5868)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun object::delete [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:196:1+92
procedure {:inline 1} $2_object_delete(_$t0: $2_object_UID) returns ()
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t2: int;
    var $t3: int;
    var $t0: $2_object_UID;
    var $temp_0'$2_object_UID': $2_object_UID;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[id]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:196:1+1
    assume {:print "$at(118,6209,6210)"} true;
    assume {:print "$track_local(78,17,0,$2_object_UID):", $t0} $t0 == $t0;

    // $t1 := unpack object::UID($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:197:9+24
    assume {:print "$at(118,6246,6270)"} true;
    $t1 := $t0->$id;

    // $t2 := unpack object::ID($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:197:19+12
    $t2 := $t1->$bytes;

    // object::delete_impl($t2) on_abort goto L2 with $t3 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:198:5+18
    assume {:print "$at(118,6281,6299)"} true;
    call $2_object_delete_impl($t2);
    if ($abort_flag) {
        assume {:print "$at(118,6281,6299)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(78,17):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:199:1+1
    assume {:print "$at(118,6300,6301)"} true;
L1:

    // return () at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:199:1+1
    assume {:print "$at(118,6300,6301)"} true;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:199:1+1
L2:

    // abort($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/object.move:199:1+1
    assume {:print "$at(118,6300,6301)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct balance::Balance<ika::IKA> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:31:1+62
datatype $2_balance_Balance'$0_ika_IKA' {
    $2_balance_Balance'$0_ika_IKA'($value: int)
}
function {:inline} $Update'$2_balance_Balance'$0_ika_IKA''_value(s: $2_balance_Balance'$0_ika_IKA', x: int): $2_balance_Balance'$0_ika_IKA' {
    $2_balance_Balance'$0_ika_IKA'(x)
}
function $IsValid'$2_balance_Balance'$0_ika_IKA''(s: $2_balance_Balance'$0_ika_IKA'): bool {
    $IsValid'u64'(s->$value)
}
function {:inline} $IsEqual'$2_balance_Balance'$0_ika_IKA''(s1: $2_balance_Balance'$0_ika_IKA', s2: $2_balance_Balance'$0_ika_IKA'): bool {
    s1 == s2
}
procedure {:inline 1} $0_prover_type_inv'$2_balance_Balance'$0_ika_IKA''(s: $2_balance_Balance'$0_ika_IKA') returns (res: bool) {
    res := true;
    return;
}

// fun balance::value<ika::IKA> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:36:1+62
procedure {:inline 1} $2_balance_value'$0_ika_IKA'(_$t0: $2_balance_Balance'$0_ika_IKA') returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $2_balance_Balance'$0_ika_IKA';
    var $temp_0'$2_balance_Balance'$0_ika_IKA'': $2_balance_Balance'$0_ika_IKA';
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:36:1+1
    assume {:print "$at(87,1210,1211)"} true;
    assume {:print "$track_local(88,0,0,$2_balance_Balance'$0_ika_IKA'):", $t0} $t0 == $t0;

    // $t1 := get_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:37:5+10
    assume {:print "$at(87,1260,1270)"} true;
    $t1 := $t0->$value;

    // trace_return[0]($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:37:5+10
    assume {:print "$track_return(88,0,0,u64):", $t1} $t1 == $t1;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:38:1+1
    assume {:print "$at(87,1271,1272)"} true;
L1:

    // return $t1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:38:1+1
    assume {:print "$at(87,1271,1272)"} true;
    $ret0 := $t1;
    return;

}

// fun balance::split<ika::IKA> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:78:1+175
procedure {:inline 1} $2_balance_split'$0_ika_IKA'(_$t0: $Mutation ($2_balance_Balance'$0_ika_IKA'), _$t1: int) returns ($ret0: $2_balance_Balance'$0_ika_IKA', $ret1: $Mutation ($2_balance_Balance'$0_ika_IKA'))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation (int);
    var $t9: $2_balance_Balance'$0_ika_IKA';
    var $t0: $Mutation ($2_balance_Balance'$0_ika_IKA');
    var $t1: int;
    var $temp_0'$2_balance_Balance'$0_ika_IKA'': $2_balance_Balance'$0_ika_IKA';
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:78:1+1
    assume {:print "$at(87,2394,2395)"} true;
    $temp_0'$2_balance_Balance'$0_ika_IKA'' := $Dereference($t0);
    assume {:print "$track_local(88,7,0,$2_balance_Balance'$0_ika_IKA'):", $temp_0'$2_balance_Balance'$0_ika_IKA''} $temp_0'$2_balance_Balance'$0_ika_IKA'' == $temp_0'$2_balance_Balance'$0_ika_IKA'';

    // trace_local[value]($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:78:1+1
    assume {:print "$track_local(88,7,1,u64):", $t1} $t1 == $t1;

    // $t2 := get_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:13+10
    assume {:print "$at(87,2475,2485)"} true;
    $t2 := $Dereference($t0)->$value;

    // $t3 := >=($t2, $t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:24+2
    call $t3 := $Ge($t2, $t1);

    // if ($t3) goto L1 else goto L0 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
L1:

    // goto L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
    assume {:print "$at(87,2467,2507)"} true;
    goto L2;

    // label L0 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
L0:

    // destroy($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
    assume {:print "$at(87,2467,2507)"} true;

    // $t4 := 2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:34+10
    $t4 := 2;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
    assume {:print "$at(87,2467,2507)"} true;
    assume {:print "$track_abort(88,7):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
    $t5 := $t4;

    // goto L4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:79:5+40
    goto L4;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:18+4
    assume {:print "$at(87,2526,2530)"} true;
L2:

    // $t6 := get_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:18+10
    assume {:print "$at(87,2526,2536)"} true;
    $t6 := $Dereference($t0)->$value;

    // $t7 := -($t6, $t1) on_abort goto L4 with $t5 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:29+1
    call $t7 := $Sub($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(87,2537,2538)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(88,7):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t8 := borrow_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:5+10
    $t8 := $ChildMutation($t0, 0, $Dereference($t0)->$value);

    // write_ref($t8, $t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:5+31
    $t8 := $UpdateMutation($t8, $t7);

    // write_back[Reference($t0).value (u64)]($t8) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:5+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'$0_ika_IKA''_value($Dereference($t0), $Dereference($t8)));

    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:80:5+31
    $temp_0'$2_balance_Balance'$0_ika_IKA'' := $Dereference($t0);
    assume {:print "$track_local(88,7,0,$2_balance_Balance'$0_ika_IKA'):", $temp_0'$2_balance_Balance'$0_ika_IKA''} $temp_0'$2_balance_Balance'$0_ika_IKA'' == $temp_0'$2_balance_Balance'$0_ika_IKA'';

    // $t9 := pack balance::Balance<#0>($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+17
    assume {:print "$at(87,2550,2567)"} true;
    $t9 := $2_balance_Balance'$0_ika_IKA'($t1);

    // trace_return[0]($t9) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+17
    assume {:print "$track_return(88,7,0,$2_balance_Balance'$0_ika_IKA'):", $t9} $t9 == $t9;

    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+17
    $temp_0'$2_balance_Balance'$0_ika_IKA'' := $Dereference($t0);
    assume {:print "$track_local(88,7,0,$2_balance_Balance'$0_ika_IKA'):", $temp_0'$2_balance_Balance'$0_ika_IKA''} $temp_0'$2_balance_Balance'$0_ika_IKA'' == $temp_0'$2_balance_Balance'$0_ika_IKA'';

    // label L3 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:82:1+1
    assume {:print "$at(87,2568,2569)"} true;
L3:

    // return $t9 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:82:1+1
    assume {:print "$at(87,2568,2569)"} true;
    $ret0 := $t9;
    $ret1 := $t0;
    return;

    // label L4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:82:1+1
L4:

    // abort($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:82:1+1
    assume {:print "$at(87,2568,2569)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun balance::join<ika::IKA> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:71:1+160
procedure {:inline 1} $2_balance_join'$0_ika_IKA'(_$t0: $Mutation ($2_balance_Balance'$0_ika_IKA'), _$t1: $2_balance_Balance'$0_ika_IKA') returns ($ret0: int, $ret1: $Mutation ($2_balance_Balance'$0_ika_IKA'))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t8: int;
    var $t0: $Mutation ($2_balance_Balance'$0_ika_IKA');
    var $t1: $2_balance_Balance'$0_ika_IKA';
    var $temp_0'$2_balance_Balance'$0_ika_IKA'': $2_balance_Balance'$0_ika_IKA';
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:71:1+1
    assume {:print "$at(87,2178,2179)"} true;
    $temp_0'$2_balance_Balance'$0_ika_IKA'' := $Dereference($t0);
    assume {:print "$track_local(88,6,0,$2_balance_Balance'$0_ika_IKA'):", $temp_0'$2_balance_Balance'$0_ika_IKA''} $temp_0'$2_balance_Balance'$0_ika_IKA'' == $temp_0'$2_balance_Balance'$0_ika_IKA'';

    // trace_local[balance]($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:71:1+1
    assume {:print "$track_local(88,6,1,$2_balance_Balance'$0_ika_IKA'):", $t1} $t1 == $t1;

    // $t3 := unpack balance::Balance<#0>($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:72:9+17
    assume {:print "$at(87,2256,2273)"} true;
    $t3 := $t1->$value;

    // trace_local[value#1#0]($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:72:19+5
    assume {:print "$track_local(88,6,2,u64):", $t3} $t3 == $t3;

    // $t4 := get_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:73:18+10
    assume {:print "$at(87,2302,2312)"} true;
    $t4 := $Dereference($t0)->$value;

    // $t5 := +($t4, $t3) on_abort goto L2 with $t6 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:73:29+1
    call $t5 := $AddU64($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(87,2313,2314)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(88,6):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:73:5+10
    $t7 := $ChildMutation($t0, 0, $Dereference($t0)->$value);

    // write_ref($t7, $t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:73:5+31
    $t7 := $UpdateMutation($t7, $t5);

    // write_back[Reference($t0).value (u64)]($t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:73:5+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'$0_ika_IKA''_value($Dereference($t0), $Dereference($t7)));

    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:73:5+31
    $temp_0'$2_balance_Balance'$0_ika_IKA'' := $Dereference($t0);
    assume {:print "$track_local(88,6,0,$2_balance_Balance'$0_ika_IKA'):", $temp_0'$2_balance_Balance'$0_ika_IKA''} $temp_0'$2_balance_Balance'$0_ika_IKA'' == $temp_0'$2_balance_Balance'$0_ika_IKA'';

    // $t8 := get_field<balance::Balance<#0>>.value($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:74:5+10
    assume {:print "$at(87,2326,2336)"} true;
    $t8 := $Dereference($t0)->$value;

    // trace_return[0]($t8) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:74:5+10
    assume {:print "$track_return(88,6,0,u64):", $t8} $t8 == $t8;

    // trace_local[self]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:74:5+10
    $temp_0'$2_balance_Balance'$0_ika_IKA'' := $Dereference($t0);
    assume {:print "$track_local(88,6,0,$2_balance_Balance'$0_ika_IKA'):", $temp_0'$2_balance_Balance'$0_ika_IKA''} $temp_0'$2_balance_Balance'$0_ika_IKA'' == $temp_0'$2_balance_Balance'$0_ika_IKA'';

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:75:1+1
    assume {:print "$at(87,2337,2338)"} true;
L1:

    // return $t8 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:75:1+1
    assume {:print "$at(87,2337,2338)"} true;
    $ret0 := $t8;
    $ret1 := $t0;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:75:1+1
L2:

    // abort($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/balance.move:75:1+1
    assume {:print "$at(87,2337,2338)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// struct ika::IKA at ./../ika/sources/ika.move:28:1+29
datatype $0_ika_IKA {
    $0_ika_IKA($dummy_field: bool)
}
function {:inline} $Update'$0_ika_IKA'_dummy_field(s: $0_ika_IKA, x: bool): $0_ika_IKA {
    $0_ika_IKA(x)
}
function $IsValid'$0_ika_IKA'(s: $0_ika_IKA): bool {
    $IsValid'bool'(s->$dummy_field)
}
function {:inline} $IsEqual'$0_ika_IKA'(s1: $0_ika_IKA, s2: $0_ika_IKA): bool {
    s1 == s2
}
procedure {:inline 1} $0_prover_type_inv'$0_ika_IKA'(s: $0_ika_IKA) returns (res: bool) {
    res := true;
    return;
}

// struct group_ops::Element<bls12381::UncompressedG1> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/crypto/group_ops.move:22:1+81
datatype $2_group_ops_Element'$2_bls12381_UncompressedG1' {
    $2_group_ops_Element'$2_bls12381_UncompressedG1'($bytes: Vec (int))
}
function {:inline} $Update'$2_group_ops_Element'$2_bls12381_UncompressedG1''_bytes(s: $2_group_ops_Element'$2_bls12381_UncompressedG1', x: Vec (int)): $2_group_ops_Element'$2_bls12381_UncompressedG1' {
    $2_group_ops_Element'$2_bls12381_UncompressedG1'(x)
}
function $IsValid'$2_group_ops_Element'$2_bls12381_UncompressedG1''(s: $2_group_ops_Element'$2_bls12381_UncompressedG1'): bool {
    $IsValid'vec'u8''(s->$bytes)
}
function {:inline} $IsEqual'$2_group_ops_Element'$2_bls12381_UncompressedG1''(s1: $2_group_ops_Element'$2_bls12381_UncompressedG1', s2: $2_group_ops_Element'$2_bls12381_UncompressedG1'): bool {
    $IsEqual'vec'u8''(s1->$bytes, s2->$bytes)}
procedure {:inline 1} $0_prover_type_inv'$2_group_ops_Element'$2_bls12381_UncompressedG1''(s: $2_group_ops_Element'$2_bls12381_UncompressedG1') returns (res: bool) {
    res := true;
    return;
}

// struct bls12381::UncompressedG1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/crypto/bls12381.move:40:1+31
datatype $2_bls12381_UncompressedG1 {
    $2_bls12381_UncompressedG1($dummy_field: bool)
}
function {:inline} $Update'$2_bls12381_UncompressedG1'_dummy_field(s: $2_bls12381_UncompressedG1, x: bool): $2_bls12381_UncompressedG1 {
    $2_bls12381_UncompressedG1(x)
}
function $IsValid'$2_bls12381_UncompressedG1'(s: $2_bls12381_UncompressedG1): bool {
    $IsValid'bool'(s->$dummy_field)
}
function {:inline} $IsEqual'$2_bls12381_UncompressedG1'(s1: $2_bls12381_UncompressedG1, s2: $2_bls12381_UncompressedG1): bool {
    s1 == s2
}
procedure {:inline 1} $0_prover_type_inv'$2_bls12381_UncompressedG1'(s: $2_bls12381_UncompressedG1) returns (res: bool) {
    res := true;
    return;
}

// struct staked_ika::StakedIka at ./../ika_system/sources/staking/staked_ika.move:47:1+336
datatype $0_staked_ika_StakedIka {
    $0_staked_ika_StakedIka($id: $2_object_UID, $state: $0_staked_ika_StakedIkaState, $validator_id: $2_object_ID, $principal: $2_balance_Balance'$0_ika_IKA', $activation_epoch: int)
}
function {:inline} $Update'$0_staked_ika_StakedIka'_id(s: $0_staked_ika_StakedIka, x: $2_object_UID): $0_staked_ika_StakedIka {
    $0_staked_ika_StakedIka(x, s->$state, s->$validator_id, s->$principal, s->$activation_epoch)
}
function {:inline} $Update'$0_staked_ika_StakedIka'_state(s: $0_staked_ika_StakedIka, x: $0_staked_ika_StakedIkaState): $0_staked_ika_StakedIka {
    $0_staked_ika_StakedIka(s->$id, x, s->$validator_id, s->$principal, s->$activation_epoch)
}
function {:inline} $Update'$0_staked_ika_StakedIka'_validator_id(s: $0_staked_ika_StakedIka, x: $2_object_ID): $0_staked_ika_StakedIka {
    $0_staked_ika_StakedIka(s->$id, s->$state, x, s->$principal, s->$activation_epoch)
}
function {:inline} $Update'$0_staked_ika_StakedIka'_principal(s: $0_staked_ika_StakedIka, x: $2_balance_Balance'$0_ika_IKA'): $0_staked_ika_StakedIka {
    $0_staked_ika_StakedIka(s->$id, s->$state, s->$validator_id, x, s->$activation_epoch)
}
function {:inline} $Update'$0_staked_ika_StakedIka'_activation_epoch(s: $0_staked_ika_StakedIka, x: int): $0_staked_ika_StakedIka {
    $0_staked_ika_StakedIka(s->$id, s->$state, s->$validator_id, s->$principal, x)
}
function $IsValid'$0_staked_ika_StakedIka'(s: $0_staked_ika_StakedIka): bool {
    $IsValid'$2_object_UID'(s->$id)
      && $IsValid'$0_staked_ika_StakedIkaState'(s->$state)
      && $IsValid'$2_object_ID'(s->$validator_id)
      && $IsValid'$2_balance_Balance'$0_ika_IKA''(s->$principal)
      && $IsValid'u64'(s->$activation_epoch)
}
function {:inline} $IsEqual'$0_staked_ika_StakedIka'(s1: $0_staked_ika_StakedIka, s2: $0_staked_ika_StakedIka): bool {
    s1 == s2
}
procedure {:inline 1} $2_object_borrow_uid'$0_staked_ika_StakedIka'(obj: $0_staked_ika_StakedIka) returns (res: $2_object_UID) {
    res := obj->$id;
}
var $0_staked_ika_StakedIka_$memory: $Memory $0_staked_ika_StakedIka;
procedure {:inline 1} $0_prover_type_inv'$0_staked_ika_StakedIka'(s: $0_staked_ika_StakedIka) returns (res: bool) {
    res := true;
    return;
}

// enum staked_ika::StakedIkaState at ./../ika_system/sources/staking/staked_ika.move:36:1+323
datatype $0_staked_ika_StakedIkaState {
    $0_staked_ika_StakedIkaState($Withdrawing_withdraw_epoch: int, $variant_id: int)
}
procedure {:inline 1} $0_staked_ika_StakedIkaState_Staked() returns (res: $0_staked_ika_StakedIkaState) {
    res->$variant_id := 0;
    return;
}

procedure {:inline 1} $0_staked_ika_StakedIkaState_Withdrawing($Withdrawing_withdraw_epoch: int) returns (res: $0_staked_ika_StakedIkaState) {
    res->$variant_id := 1;
    res->$Withdrawing_withdraw_epoch := $Withdrawing_withdraw_epoch;
    return;
}

function {:inline} $Update'$0_staked_ika_StakedIkaState'_Withdrawing_withdraw_epoch(s: $0_staked_ika_StakedIkaState, x: int): $0_staked_ika_StakedIkaState {
    $0_staked_ika_StakedIkaState(x, s->$variant_id)
}
function $IsValid'$0_staked_ika_StakedIkaState'(e: $0_staked_ika_StakedIkaState): bool {
    $IsValid'u64'(e->$Withdrawing_withdraw_epoch)
      && 0 <= e->$variant_id && e->$variant_id < 2
}
function {:inline} $IsEqual'$0_staked_ika_StakedIkaState'(e1: $0_staked_ika_StakedIkaState, e2: $0_staked_ika_StakedIkaState): bool {
    e1->$variant_id == e2->$variant_id
      && (e1->$variant_id == 0 ==> true)
      && (e1->$variant_id == 1 ==> $IsEqual'u64'(e1->$Withdrawing_withdraw_epoch, e2->$Withdrawing_withdraw_epoch))}
procedure {:inline 1} $0_prover_type_inv'$0_staked_ika_StakedIkaState'(s: $0_staked_ika_StakedIkaState) returns (res: bool) {
    res := true;
    return;
}

// fun staked_ika::value [baseline] at ./../ika_system/sources/staking/staked_ika.move:119:1+62
procedure {:inline 1} $0_staked_ika_value$impl(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: $2_balance_Balance'$0_ika_IKA';
    var $t2: int;
    var $t3: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:119:1+1
    assume {:print "$at(246,3907,3908)"} true;
    assume {:print "$track_local(115,5,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := get_field<staked_ika::StakedIka>.principal($t0) at ./../ika_system/sources/staking/staked_ika.move:119:41+12
    $t1 := $t0->$principal;

    // $t2 := balance::value<ika::IKA>($t1) on_abort goto L2 with $t3 at ./../ika_system/sources/staking/staked_ika.move:119:41+20
    call $t2 := $2_balance_value'$0_ika_IKA'($t1);
    if ($abort_flag) {
        assume {:print "$at(246,3947,3967)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(115,5):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./../ika_system/sources/staking/staked_ika.move:119:41+20
    assume {:print "$track_return(115,5,0,u64):", $t2} $t2 == $t2;

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:119:62+1
L1:

    // return $t2 at ./../ika_system/sources/staking/staked_ika.move:119:62+1
    assume {:print "$at(246,3968,3969)"} true;
    $ret0 := $t2;
    return;

    // label L2 at ./../ika_system/sources/staking/staked_ika.move:119:62+1
L2:

    // abort($t3) at ./../ika_system/sources/staking/staked_ika.move:119:62+1
    assume {:print "$at(246,3968,3969)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun staked_ika::split [baseline] at ./../ika_system/sources/staking/staked_ika.move:182:1+629
procedure {:inline 1} $0_staked_ika_split$impl(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $0_staked_ika_StakedIka, $ret1: $Mutation ($0_staked_ika_StakedIka), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: $2_balance_Balance'$0_ika_IKA';
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: bool;
    var $t10: int;
    var $t11: $2_balance_Balance'$0_ika_IKA';
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t16: int;
    var $t17: $2_object_UID;
    var $t18: $0_staked_ika_StakedIkaState;
    var $t19: $2_object_ID;
    var $t20: $Mutation ($2_balance_Balance'$0_ika_IKA');
    var $t21: $2_balance_Balance'$0_ika_IKA';
    var $t22: int;
    var $t23: $0_staked_ika_StakedIka;
    var $t0: $Mutation ($0_staked_ika_StakedIka);
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:182:1+1
    assume {:print "$at(246,6384,6385)"} true;
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,11,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // trace_local[amount]($t1) at ./../ika_system/sources/staking/staked_ika.move:182:1+1
    assume {:print "$track_local(115,11,1,u64):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./../ika_system/sources/staking/staked_ika.move:182:1+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(115,11,2,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := get_field<staked_ika::StakedIka>.principal($t0) at ./../ika_system/sources/staking/staked_ika.move:183:13+12
    assume {:print "$at(246,6480,6492)"} true;
    $t3 := $Dereference($t0)->$principal;

    // $t4 := balance::value<ika::IKA>($t3) on_abort goto L10 with $t5 at ./../ika_system/sources/staking/staked_ika.move:183:13+20
    call $t4 := $2_balance_value'$0_ika_IKA'($t3);
    if ($abort_flag) {
        assume {:print "$at(246,6480,6500)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(115,11):", $t5} $t5 == $t5;
        goto L10;
    }

    // $t6 := >($t4, $t1) at ./../ika_system/sources/staking/staked_ika.move:183:34+1
    call $t6 := $Gt($t4, $t1);

    // if ($t6) goto L1 else goto L0 at ./../ika_system/sources/staking/staked_ika.move:183:5+54
    if ($t6) { goto L1; } else { goto L0; }

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:183:5+54
L1:

    // goto L2 at ./../ika_system/sources/staking/staked_ika.move:183:5+54
    assume {:print "$at(246,6472,6526)"} true;
    goto L2;

    // label L0 at ./../ika_system/sources/staking/staked_ika.move:183:5+54
L0:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:183:5+54
    assume {:print "$at(246,6472,6526)"} true;

    // destroy($t2) at ./../ika_system/sources/staking/staked_ika.move:183:5+54

    // $t7 := 2 at ./../ika_system/sources/staking/staked_ika.move:183:44+14
    $t7 := 2;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at ./../ika_system/sources/staking/staked_ika.move:183:5+54
    assume {:print "$at(246,6472,6526)"} true;
    assume {:print "$track_abort(115,11):", $t7} $t7 == $t7;

    // $t5 := move($t7) at ./../ika_system/sources/staking/staked_ika.move:183:5+54
    $t5 := $t7;

    // goto L10 at ./../ika_system/sources/staking/staked_ika.move:183:5+54
    goto L10;

    // label L2 at ./../ika_system/sources/staking/staked_ika.move:186:13+6
    assume {:print "$at(246,6632,6638)"} true;
L2:

    // $t8 := 1000000000 at ./../ika_system/sources/staking/staked_ika.move:186:23+21
    assume {:print "$at(246,6642,6663)"} true;
    $t8 := 1000000000;
    assume $IsValid'u64'($t8);

    // $t9 := >=($t1, $t8) at ./../ika_system/sources/staking/staked_ika.move:186:20+2
    call $t9 := $Ge($t1, $t8);

    // if ($t9) goto L4 else goto L3 at ./../ika_system/sources/staking/staked_ika.move:186:5+62
    if ($t9) { goto L4; } else { goto L3; }

    // label L4 at ./../ika_system/sources/staking/staked_ika.move:186:5+62
L4:

    // goto L5 at ./../ika_system/sources/staking/staked_ika.move:186:5+62
    assume {:print "$at(246,6624,6686)"} true;
    goto L5;

    // label L3 at ./../ika_system/sources/staking/staked_ika.move:186:5+62
L3:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:186:5+62
    assume {:print "$at(246,6624,6686)"} true;

    // destroy($t2) at ./../ika_system/sources/staking/staked_ika.move:186:5+62

    // $t10 := 4 at ./../ika_system/sources/staking/staked_ika.move:186:46+20
    $t10 := 4;
    assume $IsValid'u64'($t10);

    // trace_abort($t10) at ./../ika_system/sources/staking/staked_ika.move:186:5+62
    assume {:print "$at(246,6624,6686)"} true;
    assume {:print "$track_abort(115,11):", $t10} $t10 == $t10;

    // $t5 := move($t10) at ./../ika_system/sources/staking/staked_ika.move:186:5+62
    $t5 := $t10;

    // goto L10 at ./../ika_system/sources/staking/staked_ika.move:186:5+62
    goto L10;

    // label L5 at ./../ika_system/sources/staking/staked_ika.move:187:13+2
    assume {:print "$at(246,6700,6702)"} true;
L5:

    // $t11 := get_field<staked_ika::StakedIka>.principal($t0) at ./../ika_system/sources/staking/staked_ika.move:187:13+12
    assume {:print "$at(246,6700,6712)"} true;
    $t11 := $Dereference($t0)->$principal;

    // $t12 := balance::value<ika::IKA>($t11) on_abort goto L10 with $t5 at ./../ika_system/sources/staking/staked_ika.move:187:13+20
    call $t12 := $2_balance_value'$0_ika_IKA'($t11);
    if ($abort_flag) {
        assume {:print "$at(246,6700,6720)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(115,11):", $t5} $t5 == $t5;
        goto L10;
    }

    // $t13 := -($t12, $t1) on_abort goto L10 with $t5 at ./../ika_system/sources/staking/staked_ika.move:187:34+1
    call $t13 := $Sub($t12, $t1);
    if ($abort_flag) {
        assume {:print "$at(246,6721,6722)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(115,11):", $t5} $t5 == $t5;
        goto L10;
    }

    // $t14 := 1000000000 at ./../ika_system/sources/staking/staked_ika.move:187:46+21
    $t14 := 1000000000;
    assume $IsValid'u64'($t14);

    // $t15 := >=($t13, $t14) at ./../ika_system/sources/staking/staked_ika.move:187:43+2
    call $t15 := $Ge($t13, $t14);

    // if ($t15) goto L7 else goto L6 at ./../ika_system/sources/staking/staked_ika.move:187:5+85
    if ($t15) { goto L7; } else { goto L6; }

    // label L7 at ./../ika_system/sources/staking/staked_ika.move:187:5+85
L7:

    // goto L8 at ./../ika_system/sources/staking/staked_ika.move:187:5+85
    assume {:print "$at(246,6692,6777)"} true;
    goto L8;

    // label L6 at ./../ika_system/sources/staking/staked_ika.move:187:5+85
L6:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:187:5+85
    assume {:print "$at(246,6692,6777)"} true;

    // destroy($t2) at ./../ika_system/sources/staking/staked_ika.move:187:5+85

    // $t16 := 4 at ./../ika_system/sources/staking/staked_ika.move:187:69+20
    $t16 := 4;
    assume $IsValid'u64'($t16);

    // trace_abort($t16) at ./../ika_system/sources/staking/staked_ika.move:187:5+85
    assume {:print "$at(246,6692,6777)"} true;
    assume {:print "$track_abort(115,11):", $t16} $t16 == $t16;

    // $t5 := move($t16) at ./../ika_system/sources/staking/staked_ika.move:187:5+85
    $t5 := $t16;

    // goto L10 at ./../ika_system/sources/staking/staked_ika.move:187:5+85
    goto L10;

    // label L8 at ./../ika_system/sources/staking/staked_ika.move:190:25+3
    assume {:print "$at(246,6820,6823)"} true;
L8:

    // $t17 := object::new($t2) on_abort goto L10 with $t5 at ./../ika_system/sources/staking/staked_ika.move:190:13+16
    assume {:print "$at(246,6808,6824)"} true;
    call $t17,$t2 := $2_object_new($t2);
    if ($abort_flag) {
        assume {:print "$at(246,6808,6824)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(115,11):", $t5} $t5 == $t5;
        goto L10;
    }

    // $t18 := get_field<staked_ika::StakedIka>.state($t0) at ./../ika_system/sources/staking/staked_ika.move:191:16+8
    assume {:print "$at(246,6841,6849)"} true;
    $t18 := $Dereference($t0)->$state;

    // $t19 := get_field<staked_ika::StakedIka>.validator_id($t0) at ./../ika_system/sources/staking/staked_ika.move:192:23+15
    assume {:print "$at(246,6895,6910)"} true;
    $t19 := $Dereference($t0)->$validator_id;

    // $t20 := borrow_field<staked_ika::StakedIka>.principal($t0) at ./../ika_system/sources/staking/staked_ika.move:193:20+12
    assume {:print "$at(246,6931,6943)"} true;
    $t20 := $ChildMutation($t0, 3, $Dereference($t0)->$principal);

    // $t21 := balance::split<ika::IKA>($t20, $t1) on_abort goto L10 with $t5 at ./../ika_system/sources/staking/staked_ika.move:193:20+26
    call $t21,$t20 := $2_balance_split'$0_ika_IKA'($t20, $t1);
    if ($abort_flag) {
        assume {:print "$at(246,6931,6957)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(115,11):", $t5} $t5 == $t5;
        goto L10;
    }

    // write_back[Reference($t0).principal (balance::Balance<ika::IKA>)]($t20) at ./../ika_system/sources/staking/staked_ika.move:193:20+26
    $t0 := $UpdateMutation($t0, $Update'$0_staked_ika_StakedIka'_principal($Dereference($t0), $Dereference($t20)));

    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:193:20+26
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,11,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // $t22 := get_field<staked_ika::StakedIka>.activation_epoch($t0) at ./../ika_system/sources/staking/staked_ika.move:194:27+19
    assume {:print "$at(246,6985,7004)"} true;
    $t22 := $Dereference($t0)->$activation_epoch;

    // $t23 := pack staked_ika::StakedIka($t17, $t18, $t19, $t21, $t22) at ./../ika_system/sources/staking/staked_ika.move:189:5+227
    assume {:print "$at(246,6784,7011)"} true;
    $t23 := $0_staked_ika_StakedIka($t17, $t18, $t19, $t21, $t22);

    // trace_return[0]($t23) at ./../ika_system/sources/staking/staked_ika.move:189:5+227
    assume {:print "$track_return(115,11,0,$0_staked_ika_StakedIka):", $t23} $t23 == $t23;

    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:189:5+227
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,11,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // trace_local[ctx]($t2) at ./../ika_system/sources/staking/staked_ika.move:189:5+227
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(115,11,2,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L9 at ./../ika_system/sources/staking/staked_ika.move:196:1+1
    assume {:print "$at(246,7012,7013)"} true;
L9:

    // return $t23 at ./../ika_system/sources/staking/staked_ika.move:196:1+1
    assume {:print "$at(246,7012,7013)"} true;
    $ret0 := $t23;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L10 at ./../ika_system/sources/staking/staked_ika.move:196:1+1
L10:

    // abort($t5) at ./../ika_system/sources/staking/staked_ika.move:196:1+1
    assume {:print "$at(246,7012,7013)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun staked_ika::join [baseline] at ./../ika_system/sources/staking/staked_ika.move:150:1+1061
procedure {:inline 1} $0_staked_ika_join$impl(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: $0_staked_ika_StakedIka) returns ($ret0: $Mutation ($0_staked_ika_StakedIka))
{
    // declare local variables
    var $t2: bool;
    var $t3: $2_object_UID;
    var $t4: $2_object_UID;
    var $t5: $2_balance_Balance'$0_ika_IKA';
    var $t6: $2_balance_Balance'$0_ika_IKA';
    var $t7: $2_object_ID;
    var $t8: $2_object_ID;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: int;
    var $t16: $0_staked_ika_StakedIka;
    var $t17: bool;
    var $t18: bool;
    var $t19: int;
    var $t20: $2_object_UID;
    var $t21: $0_staked_ika_StakedIkaState;
    var $t22: $2_object_ID;
    var $t23: $2_balance_Balance'$0_ika_IKA';
    var $t24: int;
    var $t25: $Mutation ($2_balance_Balance'$0_ika_IKA');
    var $t26: int;
    var $t27: $0_staked_ika_StakedIka;
    var $t28: bool;
    var $t29: bool;
    var $t30: int;
    var $t31: $0_staked_ika_StakedIka;
    var $t32: int;
    var $t33: int;
    var $t34: bool;
    var $t35: int;
    var $t36: $2_object_UID;
    var $t37: $0_staked_ika_StakedIkaState;
    var $t38: $2_object_ID;
    var $t39: $2_balance_Balance'$0_ika_IKA';
    var $t40: int;
    var $t41: $Mutation ($2_balance_Balance'$0_ika_IKA');
    var $t42: int;
    var $t0: $Mutation ($0_staked_ika_StakedIka);
    var $t1: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'$2_balance_Balance'$0_ika_IKA'': $2_balance_Balance'$0_ika_IKA';
    var $temp_0'$2_object_UID': $2_object_UID;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:150:1+1
    assume {:print "$at(246,5007,5008)"} true;
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,10,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // trace_local[other]($t1) at ./../ika_system/sources/staking/staked_ika.move:150:1+1
    assume {:print "$track_local(115,10,1,$0_staked_ika_StakedIka):", $t1} $t1 == $t1;

    // $t7 := get_field<staked_ika::StakedIka>.validator_id($t0) at ./../ika_system/sources/staking/staked_ika.move:151:13+15
    assume {:print "$at(246,5075,5090)"} true;
    $t7 := $Dereference($t0)->$validator_id;

    // $t8 := get_field<staked_ika::StakedIka>.validator_id($t1) at ./../ika_system/sources/staking/staked_ika.move:151:32+18
    $t8 := $t1->$validator_id;

    // $t9 := ==($t7, $t8) at ./../ika_system/sources/staking/staked_ika.move:151:29+2
    $t9 := $IsEqual'$2_object_ID'($t7, $t8);

    // if ($t9) goto L1 else goto L0 at ./../ika_system/sources/staking/staked_ika.move:151:5+65
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:151:5+65
L1:

    // goto L2 at ./../ika_system/sources/staking/staked_ika.move:151:5+65
    assume {:print "$at(246,5067,5132)"} true;
    goto L2;

    // label L0 at ./../ika_system/sources/staking/staked_ika.move:151:5+65
L0:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:151:5+65
    assume {:print "$at(246,5067,5132)"} true;

    // $t10 := 1 at ./../ika_system/sources/staking/staked_ika.move:151:52+17
    $t10 := 1;
    assume $IsValid'u64'($t10);

    // trace_abort($t10) at ./../ika_system/sources/staking/staked_ika.move:151:5+65
    assume {:print "$at(246,5067,5132)"} true;
    assume {:print "$track_abort(115,10):", $t10} $t10 == $t10;

    // $t11 := move($t10) at ./../ika_system/sources/staking/staked_ika.move:151:5+65
    $t11 := $t10;

    // goto L21 at ./../ika_system/sources/staking/staked_ika.move:151:5+65
    goto L21;

    // label L2 at ./../ika_system/sources/staking/staked_ika.move:152:13+2
    assume {:print "$at(246,5146,5148)"} true;
L2:

    // $t12 := get_field<staked_ika::StakedIka>.activation_epoch($t0) at ./../ika_system/sources/staking/staked_ika.move:152:13+19
    assume {:print "$at(246,5146,5165)"} true;
    $t12 := $Dereference($t0)->$activation_epoch;

    // $t13 := get_field<staked_ika::StakedIka>.activation_epoch($t1) at ./../ika_system/sources/staking/staked_ika.move:152:36+22
    $t13 := $t1->$activation_epoch;

    // $t14 := ==($t12, $t13) at ./../ika_system/sources/staking/staked_ika.move:152:33+2
    $t14 := $IsEqual'u64'($t12, $t13);

    // if ($t14) goto L4 else goto L3 at ./../ika_system/sources/staking/staked_ika.move:152:5+73
    if ($t14) { goto L4; } else { goto L3; }

    // label L4 at ./../ika_system/sources/staking/staked_ika.move:152:5+73
L4:

    // goto L5 at ./../ika_system/sources/staking/staked_ika.move:152:5+73
    assume {:print "$at(246,5138,5211)"} true;
    goto L5;

    // label L3 at ./../ika_system/sources/staking/staked_ika.move:152:5+73
L3:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:152:5+73
    assume {:print "$at(246,5138,5211)"} true;

    // $t15 := 1 at ./../ika_system/sources/staking/staked_ika.move:152:60+17
    $t15 := 1;
    assume $IsValid'u64'($t15);

    // trace_abort($t15) at ./../ika_system/sources/staking/staked_ika.move:152:5+73
    assume {:print "$at(246,5138,5211)"} true;
    assume {:print "$track_abort(115,10):", $t15} $t15 == $t15;

    // $t11 := move($t15) at ./../ika_system/sources/staking/staked_ika.move:152:5+73
    $t11 := $t15;

    // goto L21 at ./../ika_system/sources/staking/staked_ika.move:152:5+73
    goto L21;

    // label L5 at ./../ika_system/sources/staking/staked_ika.move:156:9+2
    assume {:print "$at(246,5386,5388)"} true;
L5:

    // $t16 := read_ref($t0) at ./../ika_system/sources/staking/staked_ika.move:156:9+2
    assume {:print "$at(246,5386,5388)"} true;
    $t16 := $Dereference($t0);

    // $t17 := staked_ika::is_staked($t16) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:156:9+14
    call $t17 := $0_staked_ika_is_staked($t16);
    if ($abort_flag) {
        assume {:print "$at(246,5386,5400)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // if ($t17) goto L7 else goto L6 at ./../ika_system/sources/staking/staked_ika.move:156:5+210
    if ($t17) { goto L7; } else { goto L6; }

    // label L7 at ./../ika_system/sources/staking/staked_ika.move:157:17+5
    assume {:print "$at(246,5420,5425)"} true;
L7:

    // $t18 := staked_ika::is_staked($t1) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:157:17+17
    assume {:print "$at(246,5420,5437)"} true;
    call $t18 := $0_staked_ika_is_staked($t1);
    if ($abort_flag) {
        assume {:print "$at(246,5420,5437)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // if ($t18) goto L9 else goto L8 at ./../ika_system/sources/staking/staked_ika.move:157:9+45
    if ($t18) { goto L9; } else { goto L8; }

    // label L9 at ./../ika_system/sources/staking/staked_ika.move:157:9+45
L9:

    // goto L10 at ./../ika_system/sources/staking/staked_ika.move:157:9+45
    assume {:print "$at(246,5412,5457)"} true;
    goto L10;

    // label L8 at ./../ika_system/sources/staking/staked_ika.move:157:9+45
L8:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:157:9+45
    assume {:print "$at(246,5412,5457)"} true;

    // $t19 := 1 at ./../ika_system/sources/staking/staked_ika.move:157:36+17
    $t19 := 1;
    assume $IsValid'u64'($t19);

    // trace_abort($t19) at ./../ika_system/sources/staking/staked_ika.move:157:9+45
    assume {:print "$at(246,5412,5457)"} true;
    assume {:print "$track_abort(115,10):", $t19} $t19 == $t19;

    // $t11 := move($t19) at ./../ika_system/sources/staking/staked_ika.move:157:9+45
    $t11 := $t19;

    // goto L21 at ./../ika_system/sources/staking/staked_ika.move:157:9+45
    goto L21;

    // label L10 at ./../ika_system/sources/staking/staked_ika.move:159:47+5
    assume {:print "$at(246,5506,5511)"} true;
L10:

    // ($t20, $t21, $t22, $t23, $t24) := unpack staked_ika::StakedIka($t1) at ./../ika_system/sources/staking/staked_ika.move:159:13+31
    assume {:print "$at(246,5472,5503)"} true;
    $t20 := $t1->$id;
    $t21 := $t1->$state;
    $t22 := $t1->$validator_id;
    $t23 := $t1->$principal;
    $t24 := $t1->$activation_epoch;

    // destroy($t24) at ./../ika_system/sources/staking/staked_ika.move:159:40+2

    // trace_local[principal#1#0]($t23) at ./../ika_system/sources/staking/staked_ika.move:159:29+9
    assume {:print "$track_local(115,10,5,$2_balance_Balance'$0_ika_IKA'):", $t23} $t23 == $t23;

    // destroy($t22) at ./../ika_system/sources/staking/staked_ika.move:159:40+2

    // destroy($t21) at ./../ika_system/sources/staking/staked_ika.move:159:40+2

    // trace_local[id#1#0]($t20) at ./../ika_system/sources/staking/staked_ika.move:159:25+2
    assume {:print "$track_local(115,10,3,$2_object_UID):", $t20} $t20 == $t20;

    // $t25 := borrow_field<staked_ika::StakedIka>.principal($t0) at ./../ika_system/sources/staking/staked_ika.move:160:9+12
    assume {:print "$at(246,5521,5533)"} true;
    $t25 := $ChildMutation($t0, 3, $Dereference($t0)->$principal);

    // $t26 := balance::join<ika::IKA>($t25, $t23) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:160:9+28
    call $t26,$t25 := $2_balance_join'$0_ika_IKA'($t25, $t23);
    if ($abort_flag) {
        assume {:print "$at(246,5521,5549)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // write_back[Reference($t0).principal (balance::Balance<ika::IKA>)]($t25) at ./../ika_system/sources/staking/staked_ika.move:160:9+28
    $t0 := $UpdateMutation($t0, $Update'$0_staked_ika_StakedIka'_principal($Dereference($t0), $Dereference($t25)));

    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:160:9+28
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,10,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // destroy($t26) at ./../ika_system/sources/staking/staked_ika.move:160:9+28

    // object::delete($t20) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:161:9+11
    assume {:print "$at(246,5559,5570)"} true;
    call $2_object_delete($t20);
    if ($abort_flag) {
        assume {:print "$at(246,5559,5570)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:162:9+6
    assume {:print "$at(246,5580,5586)"} true;
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,10,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // goto L20 at ./../ika_system/sources/staking/staked_ika.move:162:9+6
    goto L20;

    // label L6 at ./../ika_system/sources/staking/staked_ika.move:168:13+2
    assume {:print "$at(246,5820,5822)"} true;
L6:

    // $t27 := read_ref($t0) at ./../ika_system/sources/staking/staked_ika.move:168:13+2
    assume {:print "$at(246,5820,5822)"} true;
    $t27 := $Dereference($t0);

    // $t28 := staked_ika::is_withdrawing($t27) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:168:13+19
    call $t28 := $0_staked_ika_is_withdrawing($t27);
    if ($abort_flag) {
        assume {:print "$at(246,5820,5839)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // if ($t28) goto L12 else goto L11 at ./../ika_system/sources/staking/staked_ika.move:168:13+45
    if ($t28) { goto L12; } else { goto L11; }

    // label L12 at ./../ika_system/sources/staking/staked_ika.move:168:36+5
L12:

    // $t2 := staked_ika::is_withdrawing($t1) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:168:36+22
    assume {:print "$at(246,5843,5865)"} true;
    call $t2 := $0_staked_ika_is_withdrawing($t1);
    if ($abort_flag) {
        assume {:print "$at(246,5843,5865)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // goto L13 at ./../ika_system/sources/staking/staked_ika.move:168:13+45
    goto L13;

    // label L11 at ./../ika_system/sources/staking/staked_ika.move:168:13+45
L11:

    // $t29 := false at ./../ika_system/sources/staking/staked_ika.move:168:13+45
    assume {:print "$at(246,5820,5865)"} true;
    $t29 := false;
    assume $IsValid'bool'($t29);

    // $t2 := $t29 at ./../ika_system/sources/staking/staked_ika.move:168:13+45
    $t2 := $t29;

    // label L13 at ./../ika_system/sources/staking/staked_ika.move:168:13+45
L13:

    // if ($t2) goto L15 else goto L14 at ./../ika_system/sources/staking/staked_ika.move:168:5+73
    assume {:print "$at(246,5812,5885)"} true;
    if ($t2) { goto L15; } else { goto L14; }

    // label L15 at ./../ika_system/sources/staking/staked_ika.move:168:5+73
L15:

    // goto L16 at ./../ika_system/sources/staking/staked_ika.move:168:5+73
    assume {:print "$at(246,5812,5885)"} true;
    goto L16;

    // label L14 at ./../ika_system/sources/staking/staked_ika.move:168:5+73
L14:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:168:5+73
    assume {:print "$at(246,5812,5885)"} true;

    // $t30 := 1 at ./../ika_system/sources/staking/staked_ika.move:168:60+17
    $t30 := 1;
    assume $IsValid'u64'($t30);

    // trace_abort($t30) at ./../ika_system/sources/staking/staked_ika.move:168:5+73
    assume {:print "$at(246,5812,5885)"} true;
    assume {:print "$track_abort(115,10):", $t30} $t30 == $t30;

    // $t11 := move($t30) at ./../ika_system/sources/staking/staked_ika.move:168:5+73
    $t11 := $t30;

    // goto L21 at ./../ika_system/sources/staking/staked_ika.move:168:5+73
    goto L21;

    // label L16 at ./../ika_system/sources/staking/staked_ika.move:169:13+2
    assume {:print "$at(246,5899,5901)"} true;
L16:

    // $t31 := read_ref($t0) at ./../ika_system/sources/staking/staked_ika.move:169:13+2
    assume {:print "$at(246,5899,5901)"} true;
    $t31 := $Dereference($t0);

    // $t32 := staked_ika::withdraw_epoch($t31) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:169:13+19
    call $t32 := $0_staked_ika_withdraw_epoch($t31);
    if ($abort_flag) {
        assume {:print "$at(246,5899,5918)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // $t33 := staked_ika::withdraw_epoch($t1) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:169:36+22
    call $t33 := $0_staked_ika_withdraw_epoch($t1);
    if ($abort_flag) {
        assume {:print "$at(246,5922,5944)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // $t34 := ==($t32, $t33) at ./../ika_system/sources/staking/staked_ika.move:169:33+2
    $t34 := $IsEqual'u64'($t32, $t33);

    // if ($t34) goto L18 else goto L17 at ./../ika_system/sources/staking/staked_ika.move:169:5+73
    if ($t34) { goto L18; } else { goto L17; }

    // label L18 at ./../ika_system/sources/staking/staked_ika.move:169:5+73
L18:

    // goto L19 at ./../ika_system/sources/staking/staked_ika.move:169:5+73
    assume {:print "$at(246,5891,5964)"} true;
    goto L19;

    // label L17 at ./../ika_system/sources/staking/staked_ika.move:169:5+73
L17:

    // destroy($t0) at ./../ika_system/sources/staking/staked_ika.move:169:5+73
    assume {:print "$at(246,5891,5964)"} true;

    // $t35 := 1 at ./../ika_system/sources/staking/staked_ika.move:169:60+17
    $t35 := 1;
    assume $IsValid'u64'($t35);

    // trace_abort($t35) at ./../ika_system/sources/staking/staked_ika.move:169:5+73
    assume {:print "$at(246,5891,5964)"} true;
    assume {:print "$track_abort(115,10):", $t35} $t35 == $t35;

    // $t11 := move($t35) at ./../ika_system/sources/staking/staked_ika.move:169:5+73
    $t11 := $t35;

    // goto L21 at ./../ika_system/sources/staking/staked_ika.move:169:5+73
    goto L21;

    // label L19 at ./../ika_system/sources/staking/staked_ika.move:171:43+5
    assume {:print "$at(246,6009,6014)"} true;
L19:

    // ($t36, $t37, $t38, $t39, $t40) := unpack staked_ika::StakedIka($t1) at ./../ika_system/sources/staking/staked_ika.move:171:9+31
    assume {:print "$at(246,5975,6006)"} true;
    $t36 := $t1->$id;
    $t37 := $t1->$state;
    $t38 := $t1->$validator_id;
    $t39 := $t1->$principal;
    $t40 := $t1->$activation_epoch;

    // destroy($t40) at ./../ika_system/sources/staking/staked_ika.move:171:36+2

    // trace_local[principal#2#0]($t39) at ./../ika_system/sources/staking/staked_ika.move:171:25+9
    assume {:print "$track_local(115,10,6,$2_balance_Balance'$0_ika_IKA'):", $t39} $t39 == $t39;

    // destroy($t38) at ./../ika_system/sources/staking/staked_ika.move:171:36+2

    // destroy($t37) at ./../ika_system/sources/staking/staked_ika.move:171:36+2

    // trace_local[id#2#0]($t36) at ./../ika_system/sources/staking/staked_ika.move:171:21+2
    assume {:print "$track_local(115,10,4,$2_object_UID):", $t36} $t36 == $t36;

    // $t41 := borrow_field<staked_ika::StakedIka>.principal($t0) at ./../ika_system/sources/staking/staked_ika.move:172:5+12
    assume {:print "$at(246,6020,6032)"} true;
    $t41 := $ChildMutation($t0, 3, $Dereference($t0)->$principal);

    // $t42 := balance::join<ika::IKA>($t41, $t39) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:172:5+28
    call $t42,$t41 := $2_balance_join'$0_ika_IKA'($t41, $t39);
    if ($abort_flag) {
        assume {:print "$at(246,6020,6048)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // write_back[Reference($t0).principal (balance::Balance<ika::IKA>)]($t41) at ./../ika_system/sources/staking/staked_ika.move:172:5+28
    $t0 := $UpdateMutation($t0, $Update'$0_staked_ika_StakedIka'_principal($Dereference($t0), $Dereference($t41)));

    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:172:5+28
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,10,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // destroy($t42) at ./../ika_system/sources/staking/staked_ika.move:172:5+28

    // object::delete($t36) on_abort goto L21 with $t11 at ./../ika_system/sources/staking/staked_ika.move:173:5+11
    assume {:print "$at(246,6054,6065)"} true;
    call $2_object_delete($t36);
    if ($abort_flag) {
        assume {:print "$at(246,6054,6065)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(115,10):", $t11} $t11 == $t11;
        goto L21;
    }

    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:173:16+1
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(115,10,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // label L20 at ./../ika_system/sources/staking/staked_ika.move:174:1+1
    assume {:print "$at(246,6067,6068)"} true;
L20:

    // return () at ./../ika_system/sources/staking/staked_ika.move:174:1+1
    assume {:print "$at(246,6067,6068)"} true;
    $ret0 := $t0;
    return;

    // label L21 at ./../ika_system/sources/staking/staked_ika.move:174:1+1
L21:

    // abort($t11) at ./../ika_system/sources/staking/staked_ika.move:174:1+1
    assume {:print "$at(246,6067,6068)"} true;
    $abort_code := $t11;
    $abort_flag := true;
    return;

}

// fun staked_ika::validator_id [baseline] at ./../ika_system/sources/staking/staked_ika.move:115:1+63
procedure {:inline 1} $0_staked_ika_validator_id$impl(_$t0: $0_staked_ika_StakedIka) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:115:1+1
    assume {:print "$at(246,3746,3747)"} true;
    assume {:print "$track_local(115,4,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := get_field<staked_ika::StakedIka>.validator_id($t0) at ./../ika_system/sources/staking/staked_ika.move:115:47+15
    $t1 := $t0->$validator_id;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/staked_ika.move:115:47+15
    assume {:print "$track_return(115,4,0,$2_object_ID):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:115:63+1
L1:

    // return $t1 at ./../ika_system/sources/staking/staked_ika.move:115:63+1
    assume {:print "$at(246,3808,3809)"} true;
    $ret0 := $t1;
    return;

}

// fun staked_ika::activation_epoch [baseline] at ./../ika_system/sources/staking/staked_ika.move:122:1+72
procedure {:inline 1} $0_staked_ika_activation_epoch$impl(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:122:1+1
    assume {:print "$at(246,4025,4026)"} true;
    assume {:print "$track_local(115,6,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := get_field<staked_ika::StakedIka>.activation_epoch($t0) at ./../ika_system/sources/staking/staked_ika.move:122:52+19
    $t1 := $t0->$activation_epoch;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/staked_ika.move:122:52+19
    assume {:print "$track_return(115,6,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:122:72+1
L1:

    // return $t1 at ./../ika_system/sources/staking/staked_ika.move:122:72+1
    assume {:print "$at(246,4096,4097)"} true;
    $ret0 := $t1;
    return;

}

// fun staked_ika::is_staked [baseline] at ./../ika_system/sources/staking/staked_ika.move:125:1+81
procedure {:inline 1} $0_staked_ika_is_staked$impl(_$t0: $0_staked_ika_StakedIka) returns ($ret0: bool)
{
    // declare local variables
    var $t1: $0_staked_ika_StakedIkaState;
    var $t2: $0_staked_ika_StakedIkaState;
    var $t3: bool;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'bool': bool;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:125:1+1
    assume {:print "$at(246,4160,4161)"} true;
    assume {:print "$track_local(115,7,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := get_field<staked_ika::StakedIka>.state($t0) at ./../ika_system/sources/staking/staked_ika.move:125:46+8
    $t1 := $t0->$state;

    // $t2 := pack_variant<staked_ika::StakedIkaState>::Staked() at ./../ika_system/sources/staking/staked_ika.move:125:58+22
    call $t2 := $0_staked_ika_StakedIkaState_Staked();

    // $t3 := ==($t1, $t2) at ./../ika_system/sources/staking/staked_ika.move:125:55+2
    $t3 := $IsEqual'$0_staked_ika_StakedIkaState'($t1, $t2);

    // trace_return[0]($t3) at ./../ika_system/sources/staking/staked_ika.move:125:46+34
    assume {:print "$track_return(115,7,0,bool):", $t3} $t3 == $t3;

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:125:81+1
L1:

    // return $t3 at ./../ika_system/sources/staking/staked_ika.move:125:81+1
    assume {:print "$at(246,4240,4241)"} true;
    $ret0 := $t3;
    return;

}

// fun staked_ika::is_withdrawing [baseline] at ./../ika_system/sources/staking/staked_ika.move:128:1+152
procedure {:inline 1} $0_staked_ika_is_withdrawing$impl(_$t0: $0_staked_ika_StakedIka) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: $0_staked_ika_StakedIkaState;
    var $t3: $0_staked_ika_StakedIkaState;
    var $t4: $0_staked_ika_StakedIkaState;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'bool': bool;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:128:1+1
    assume {:print "$at(246,4308,4309)"} true;
    assume {:print "$track_local(115,8,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t4 := get_field<staked_ika::StakedIka>.state($t0) at ./../ika_system/sources/staking/staked_ika.move:129:12+8
    assume {:print "$at(246,4369,4377)"} true;
    $t4 := $t0->$state;

    // switch $t4 { 0 => L0 1 => L1} at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    if ($t4->$variant_id == 0) { goto L0; }
    if ($t4->$variant_id == 1) { goto L1; }

    // label L0 at ./../ika_system/sources/staking/staked_ika.move:131:14+5
    assume {:print "$at(246,4446,4451)"} true;
L0:

    // $t5 := false at ./../ika_system/sources/staking/staked_ika.move:131:14+5
    assume {:print "$at(246,4446,4451)"} true;
    $t5 := false;
    assume $IsValid'bool'($t5);

    // $t1 := $t5 at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    assume {:print "$at(246,4379,4458)"} true;
    $t1 := $t5;

    // goto L2 at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    goto L2;

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:129:22+79
L1:

    // $t6 := &unpack_variant<staked_ika::StakedIkaState>::Withdrawing($t4) at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    assume {:print "$at(246,4379,4458)"} true;
    $t6 := $t4->$Withdrawing_withdraw_epoch;

    // $t7 := unpack_variant<staked_ika::StakedIkaState>::Withdrawing($t4) at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    $t7 := $t4->$Withdrawing_withdraw_epoch;

    // destroy($t7) at ./../ika_system/sources/staking/staked_ika.move:130:9+34
    assume {:print "$at(246,4389,4423)"} true;

    // $t8 := true at ./../ika_system/sources/staking/staked_ika.move:130:47+4
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t1 := $t8 at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    assume {:print "$at(246,4379,4458)"} true;
    $t1 := $t8;

    // label L2 at ./../ika_system/sources/staking/staked_ika.move:129:22+79
L2:

    // trace_return[0]($t1) at ./../ika_system/sources/staking/staked_ika.move:129:22+79
    assume {:print "$at(246,4379,4458)"} true;
    assume {:print "$track_return(115,8,0,bool):", $t1} $t1 == $t1;

    // label L3 at ./../ika_system/sources/staking/staked_ika.move:133:1+1
    assume {:print "$at(246,4459,4460)"} true;
L3:

    // return $t1 at ./../ika_system/sources/staking/staked_ika.move:133:1+1
    assume {:print "$at(246,4459,4460)"} true;
    $ret0 := $t1;
    return;

}

// fun staked_ika::withdraw_epoch [baseline] at ./../ika_system/sources/staking/staked_ika.move:137:1+193
procedure {:inline 1} $0_staked_ika_withdraw_epoch$impl(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: $0_staked_ika_StakedIkaState;
    var $t2: $0_staked_ika_StakedIkaState;
    var $t3: $0_staked_ika_StakedIkaState;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./../ika_system/sources/staking/staked_ika.move:137:1+1
    assume {:print "$at(246,4566,4567)"} true;
    assume {:print "$track_local(115,9,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t3 := get_field<staked_ika::StakedIka>.state($t0) at ./../ika_system/sources/staking/staked_ika.move:138:12+8
    assume {:print "$at(246,4626,4634)"} true;
    $t3 := $t0->$state;

    // switch $t3 { 0 => L0 1 => L1} at ./../ika_system/sources/staking/staked_ika.move:138:22+121
    if ($t3->$variant_id == 0) { goto L0; }
    if ($t3->$variant_id == 1) { goto L1; }

    // label L0 at ./../ika_system/sources/staking/staked_ika.move:140:14+21
    assume {:print "$at(246,4729,4750)"} true;
L0:

    // $t4 := 0 at ./../ika_system/sources/staking/staked_ika.move:140:20+15
    assume {:print "$at(246,4735,4750)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at ./../ika_system/sources/staking/staked_ika.move:140:14+21
    assume {:print "$at(246,4729,4750)"} true;
    assume {:print "$track_abort(115,9):", $t4} $t4 == $t4;

    // goto L3 at ./../ika_system/sources/staking/staked_ika.move:140:14+21
    goto L3;

    // label L1 at ./../ika_system/sources/staking/staked_ika.move:138:22+121
    assume {:print "$at(246,4636,4757)"} true;
L1:

    // $t5 := &unpack_variant<staked_ika::StakedIkaState>::Withdrawing($t3) at ./../ika_system/sources/staking/staked_ika.move:138:22+121
    assume {:print "$at(246,4636,4757)"} true;
    $t5 := $t3->$Withdrawing_withdraw_epoch;

    // $t6 := unpack_variant<staked_ika::StakedIkaState>::Withdrawing($t3) at ./../ika_system/sources/staking/staked_ika.move:138:22+121
    $t6 := $t3->$Withdrawing_withdraw_epoch;

    // trace_return[0]($t6) at ./../ika_system/sources/staking/staked_ika.move:138:22+121
    assume {:print "$track_return(115,9,0,u64):", $t6} $t6 == $t6;

    // label L2 at ./../ika_system/sources/staking/staked_ika.move:142:1+1
    assume {:print "$at(246,4758,4759)"} true;
L2:

    // return $t6 at ./../ika_system/sources/staking/staked_ika.move:142:1+1
    assume {:print "$at(246,4758,4759)"} true;
    $ret0 := $t6;
    return;

    // label L3 at ./../ika_system/sources/staking/staked_ika.move:142:1+1
L3:

    // abort($t4) at ./../ika_system/sources/staking/staked_ika.move:142:1+1
    assume {:print "$at(246,4758,4759)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// struct extended_field::ExtendedField<validator_metadata::ValidatorMetadata> at ./../ika_common/sources/extended_field.move:13:1+72
datatype $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata' {
    $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata'($id: $2_object_UID)
}
function {:inline} $Update'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''_id(s: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata', x: $2_object_UID): $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata' {
    $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata'(x)
}
function $IsValid'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''(s: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata'): bool {
    $IsValid'$2_object_UID'(s->$id)
}
function {:inline} $IsEqual'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''(s1: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata', s2: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata'): bool {
    s1 == s2
}
procedure {:inline 1} $2_object_borrow_uid'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''(obj: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata') returns (res: $2_object_UID) {
    res := obj->$id;
}
var $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata'_$memory: $Memory $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata';
procedure {:inline 1} $0_prover_type_inv'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''(s: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata') returns (res: bool) {
    res := true;
    return;
}

// fun prover::drop_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+39
procedure $0_prover_drop'#0'$opaque(_$t0: #0) returns ();

procedure {:inline 1} $0_prover_drop'#0'(_$t0: #0) returns ()
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: #0;
    var $temp_0'#0': #0;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // $t1 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    $t1 := true;

    // prover::ensures($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    assert {:msg "assert_failed(4,861,862): prover::ensures does not hold"} $t1;

    // trace_local[x]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    assume {:print "$track_local(127,11,0,#0):", $t0} $t0 == $t0;

    // prover::drop<#0>($t0) on_abort goto L2 with $t2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:54:5+7
    assume {:print "$at(4,890,897)"} true;
    call $abort_if_cond := $0_prover_drop'#0'$aborts($t0);
    $abort_flag := !$abort_if_cond;
    call $0_prover_drop'#0'$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(4,890,897)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(127,11):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
L1:

    // return () at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
L2:

    // abort($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun prover::drop_spec<tx_context::TxContext> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+39
procedure $0_prover_drop'$2_tx_context_TxContext'$opaque(_$t0: $2_tx_context_TxContext) returns ();

procedure {:inline 1} $0_prover_drop'$2_tx_context_TxContext'(_$t0: $2_tx_context_TxContext) returns ()
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // $t1 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    $t1 := true;

    // prover::ensures($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    assert {:msg "assert_failed(4,861,862): prover::ensures does not hold"} $t1;

    // trace_local[x]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    assume {:print "$track_local(127,11,0,$2_tx_context_TxContext):", $t0} $t0 == $t0;

    // prover::drop<#0>($t0) on_abort goto L2 with $t2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:54:5+7
    assume {:print "$at(4,890,897)"} true;
    call $abort_if_cond := $0_prover_drop'$2_tx_context_TxContext'$aborts($t0);
    $abort_flag := !$abort_if_cond;
    call $0_prover_drop'$2_tx_context_TxContext'$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(4,890,897)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(127,11):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
L1:

    // return () at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
L2:

    // abort($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun prover::drop_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+39
procedure {:inline 1} $0_prover_drop'#0'$aborts(_$t0: #0) returns (res: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: #0;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // $t1 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    $t1 := true;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
L1:

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
L2:

    // abort($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun prover::drop_spec<tx_context::TxContext> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+39
procedure {:inline 1} $0_prover_drop'$2_tx_context_TxContext'$aborts(_$t0: $2_tx_context_TxContext) returns (res: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // $t1 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:53:1+1
    assume {:print "$at(4,861,862)"} true;
    $t1 := true;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
L1:

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
L2:

    // abort($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:55:1+1
    assume {:print "$at(4,899,900)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun prover::ref_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
procedure $0_prover_ref'#0'$opaque(_$t0: #0) returns ($ret0: #0);

procedure {:inline 1} $0_prover_ref'#0'(_$t0: #0) returns ($ret0: #0)
{
    // declare local variables
    var $t1: #0;
    var $t2: #0;
    var $t3: bool;
    var $t4: int;
    var $t5: #0;
    var $t6: #0;
    var $t7: bool;
    var $t8: bool;
    var $t0: #0;
    var $temp_0'#0': #0;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // $t3 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    $t3 := true;

    // prover::ensures($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    assert {:msg "assert_failed(4,665,666): prover::ensures does not hold"} $t3;

    // trace_local[x]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    assume {:print "$track_local(127,9,0,#0):", $t0} $t0 == $t0;

    // $t5 := prover::val<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:40:17+7
    assume {:print "$at(4,709,716)"} true;
    call $t5 := $0_prover_val'#0'($t0);

    // trace_local[old_x#1#0]($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:40:9+5
    assume {:print "$at(4,701,706)"} true;
    assume {:print "$track_local(127,9,1,#0):", $t5} $t5 == $t5;

    // $t6 := prover::ref<#0>($t0) on_abort goto L2 with $t4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:42:18+6
    assume {:print "$at(4,736,742)"} true;
    call $abort_if_cond := $0_prover_ref'#0'$aborts($t0);
    $abort_flag := !$abort_if_cond;
    call $t6 := $0_prover_ref'#0'$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(4,736,742)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(127,9):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t6 := havoc[val]() at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
    assume {:print "$at(4,665,805)"} true;
    havoc $t6;

    // assume WellFormed($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
    assume $IsValid'#0'($t6);

    // trace_local[result#1#0]($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:42:9+6
    assume {:print "$at(4,727,733)"} true;
    assume {:print "$track_local(127,9,2,#0):", $t6} $t6 == $t6;

    // $t7 := ==($t6, $t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:44:20+2
    assume {:print "$at(4,764,766)"} true;
    $t7 := $IsEqual'#0'($t6, $t5);

    // prover::requires($t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:44:5+24
    call $0_prover_requires($t7);

    // prover::drop<#0>($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:45:5+11
    assume {:print "$at(4,779,790)"} true;
    call $0_prover_drop'#0'($t5);

    // trace_return[0]($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:47:5+6
    assume {:print "$at(4,797,803)"} true;
    assume {:print "$track_return(127,9,0,#0):", $t6} $t6 == $t6;

    // $t8 := prover::type_inv<#0>($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $t8 := true;

    // prover::requires($t8) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    call $0_prover_requires($t8);

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
L1:

    // return $t6 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $ret0 := $t6;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
L2:

    // abort($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun prover::ref_spec<tx_context::TxContext> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
procedure $0_prover_ref'$2_tx_context_TxContext'$opaque(_$t0: $2_tx_context_TxContext) returns ($ret0: $2_tx_context_TxContext);

procedure {:inline 1} $0_prover_ref'$2_tx_context_TxContext'(_$t0: $2_tx_context_TxContext) returns ($ret0: $2_tx_context_TxContext)
{
    // declare local variables
    var $t1: $2_tx_context_TxContext;
    var $t2: $2_tx_context_TxContext;
    var $t3: bool;
    var $t4: int;
    var $t5: $2_tx_context_TxContext;
    var $t6: $2_tx_context_TxContext;
    var $t7: bool;
    var $t8: bool;
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // $t3 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    $t3 := true;

    // prover::ensures($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    assert {:msg "assert_failed(4,665,666): prover::ensures does not hold"} $t3;

    // trace_local[x]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    assume {:print "$track_local(127,9,0,$2_tx_context_TxContext):", $t0} $t0 == $t0;

    // $t5 := prover::val<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:40:17+7
    assume {:print "$at(4,709,716)"} true;
    call $t5 := $0_prover_val'$2_tx_context_TxContext'($t0);

    // trace_local[old_x#1#0]($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:40:9+5
    assume {:print "$at(4,701,706)"} true;
    assume {:print "$track_local(127,9,1,$2_tx_context_TxContext):", $t5} $t5 == $t5;

    // $t6 := prover::ref<#0>($t0) on_abort goto L2 with $t4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:42:18+6
    assume {:print "$at(4,736,742)"} true;
    call $abort_if_cond := $0_prover_ref'$2_tx_context_TxContext'$aborts($t0);
    $abort_flag := !$abort_if_cond;
    call $t6 := $0_prover_ref'$2_tx_context_TxContext'$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(4,736,742)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(127,9):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t6 := havoc[val]() at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
    assume {:print "$at(4,665,805)"} true;
    havoc $t6;

    // assume WellFormed($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
    assume $IsValid'$2_tx_context_TxContext'($t6);

    // trace_local[result#1#0]($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:42:9+6
    assume {:print "$at(4,727,733)"} true;
    assume {:print "$track_local(127,9,2,$2_tx_context_TxContext):", $t6} $t6 == $t6;

    // $t7 := ==($t6, $t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:44:20+2
    assume {:print "$at(4,764,766)"} true;
    $t7 := $IsEqual'$2_tx_context_TxContext'($t6, $t5);

    // prover::requires($t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:44:5+24
    call $0_prover_requires($t7);

    // prover::drop<#0>($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:45:5+11
    assume {:print "$at(4,779,790)"} true;
    call $0_prover_drop'$2_tx_context_TxContext'($t5);

    // trace_return[0]($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:47:5+6
    assume {:print "$at(4,797,803)"} true;
    assume {:print "$track_return(127,9,0,$2_tx_context_TxContext):", $t6} $t6 == $t6;

    // $t8 := prover::type_inv<#0>($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $t8 := true;

    // prover::requires($t8) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    call $0_prover_requires($t8);

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
L1:

    // return $t6 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $ret0 := $t6;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
L2:

    // abort($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun prover::ref_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
procedure {:inline 1} $0_prover_ref'#0'$aborts(_$t0: #0) returns (res: bool)
{
    // declare local variables
    var $t1: #0;
    var $t2: #0;
    var $t3: bool;
    var $t4: int;
    var $t5: #0;
    var $t6: #0;
    var $t7: bool;
    var $t8: bool;
    var $t0: #0;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // $t3 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    $t3 := true;

    // $t5 := prover::val<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:40:17+7
    assume {:print "$at(4,709,716)"} true;
    call $t5 := $0_prover_val'#0'($t0);

    // $t7 := ==($t6, $t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:44:20+2
    assume {:print "$at(4,764,766)"} true;
    $t7 := $IsEqual'#0'($t6, $t5);

    // prover::drop<#0>($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:45:5+11
    assume {:print "$at(4,779,790)"} true;
    call $0_prover_drop'#0'($t5);

    // $t8 := prover::type_inv<#0>($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $t8 := true;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
L1:

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
L2:

    // abort($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun prover::ref_spec<tx_context::TxContext> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+140
procedure {:inline 1} $0_prover_ref'$2_tx_context_TxContext'$aborts(_$t0: $2_tx_context_TxContext) returns (res: bool)
{
    // declare local variables
    var $t1: $2_tx_context_TxContext;
    var $t2: $2_tx_context_TxContext;
    var $t3: bool;
    var $t4: int;
    var $t5: $2_tx_context_TxContext;
    var $t6: $2_tx_context_TxContext;
    var $t7: bool;
    var $t8: bool;
    var $t0: $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // $t3 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:39:1+1
    assume {:print "$at(4,665,666)"} true;
    $t3 := true;

    // $t5 := prover::val<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:40:17+7
    assume {:print "$at(4,709,716)"} true;
    call $t5 := $0_prover_val'$2_tx_context_TxContext'($t0);

    // $t7 := ==($t6, $t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:44:20+2
    assume {:print "$at(4,764,766)"} true;
    $t7 := $IsEqual'$2_tx_context_TxContext'($t6, $t5);

    // prover::drop<#0>($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:45:5+11
    assume {:print "$at(4,779,790)"} true;
    call $0_prover_drop'$2_tx_context_TxContext'($t5);

    // $t8 := prover::type_inv<#0>($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $t8 := true;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
L1:

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
L2:

    // abort($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:48:1+1
    assume {:print "$at(4,804,805)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun prover::val_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+93
function $0_prover_val'#0'$opaque(_$t0: #0) returns ($ret0: #0);

procedure {:inline 1} $0_prover_val'#0'(_$t0: #0) returns ($ret0: #0)
{
    // declare local variables
    var $t1: #0;
    var $t2: bool;
    var $t3: int;
    var $t4: #0;
    var $t5: bool;
    var $t6: bool;
    var $t0: #0;
    var $temp_0'#0': #0;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // $t2 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    $t2 := true;

    // prover::ensures($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    assert {:msg "assert_failed(4,513,514): prover::ensures does not hold"} $t2;

    // trace_local[x]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    assume {:print "$track_local(127,7,0,#0):", $t0} $t0 == $t0;

    // $t4 := prover::val<#0>($t0) on_abort goto L2 with $t3 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:29:18+6
    assume {:print "$at(4,558,564)"} true;
    call $abort_if_cond := $0_prover_val'#0'$aborts($t0);
    $abort_flag := !$abort_if_cond;
    $t4 := $0_prover_val'#0'$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(4,558,564)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(127,7):", $t3} $t3 == $t3;
        goto L2;
    }

    // assume WellFormed($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+93
    assume {:print "$at(4,513,606)"} true;
    assume $IsValid'#0'($t4);

    // trace_local[result#1#0]($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:29:9+6
    assume {:print "$at(4,549,555)"} true;
    assume {:print "$track_local(127,7,1,#0):", $t4} $t4 == $t4;

    // $t5 := ==($t4, $t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:31:20+2
    assume {:print "$at(4,586,588)"} true;
    $t5 := $IsEqual'#0'($t4, $t0);

    // prover::requires($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:31:5+20
    call $0_prover_requires($t5);

    // trace_return[0]($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:33:5+6
    assume {:print "$at(4,598,604)"} true;
    assume {:print "$track_return(127,7,0,#0):", $t4} $t4 == $t4;

    // $t6 := prover::type_inv<#0>($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $t6 := true;

    // prover::requires($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    call $0_prover_requires($t6);

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
L1:

    // return $t4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
L2:

    // abort($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun prover::val_spec<tx_context::TxContext> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+93
function $0_prover_val'$2_tx_context_TxContext'$opaque(_$t0: $2_tx_context_TxContext) returns ($ret0: $2_tx_context_TxContext);

procedure {:inline 1} $0_prover_val'$2_tx_context_TxContext'(_$t0: $2_tx_context_TxContext) returns ($ret0: $2_tx_context_TxContext)
{
    // declare local variables
    var $t1: $2_tx_context_TxContext;
    var $t2: bool;
    var $t3: int;
    var $t4: $2_tx_context_TxContext;
    var $t5: bool;
    var $t6: bool;
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // $t2 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    $t2 := true;

    // prover::ensures($t2) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    assert {:msg "assert_failed(4,513,514): prover::ensures does not hold"} $t2;

    // trace_local[x]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    assume {:print "$track_local(127,7,0,$2_tx_context_TxContext):", $t0} $t0 == $t0;

    // $t4 := prover::val<#0>($t0) on_abort goto L2 with $t3 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:29:18+6
    assume {:print "$at(4,558,564)"} true;
    call $abort_if_cond := $0_prover_val'$2_tx_context_TxContext'$aborts($t0);
    $abort_flag := !$abort_if_cond;
    $t4 := $0_prover_val'$2_tx_context_TxContext'$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(4,558,564)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(127,7):", $t3} $t3 == $t3;
        goto L2;
    }

    // assume WellFormed($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+93
    assume {:print "$at(4,513,606)"} true;
    assume $IsValid'$2_tx_context_TxContext'($t4);

    // trace_local[result#1#0]($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:29:9+6
    assume {:print "$at(4,549,555)"} true;
    assume {:print "$track_local(127,7,1,$2_tx_context_TxContext):", $t4} $t4 == $t4;

    // $t5 := ==($t4, $t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:31:20+2
    assume {:print "$at(4,586,588)"} true;
    $t5 := $IsEqual'$2_tx_context_TxContext'($t4, $t0);

    // prover::requires($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:31:5+20
    call $0_prover_requires($t5);

    // trace_return[0]($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:33:5+6
    assume {:print "$at(4,598,604)"} true;
    assume {:print "$track_return(127,7,0,$2_tx_context_TxContext):", $t4} $t4 == $t4;

    // $t6 := prover::type_inv<#0>($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $t6 := true;

    // prover::requires($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    call $0_prover_requires($t6);

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
L1:

    // return $t4 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
L2:

    // abort($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun prover::val_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+93
procedure {:inline 1} $0_prover_val'#0'$aborts(_$t0: #0) returns (res: bool)
{
    // declare local variables
    var $t1: #0;
    var $t2: bool;
    var $t3: int;
    var $t4: #0;
    var $t5: bool;
    var $t6: bool;
    var $t0: #0;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // $t2 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    $t2 := true;

    // $t5 := ==($t4, $t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:31:20+2
    assume {:print "$at(4,586,588)"} true;
    $t5 := $IsEqual'#0'($t4, $t0);

    // $t6 := prover::type_inv<#0>($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $t6 := true;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
L1:

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
L2:

    // abort($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun prover::val_spec<tx_context::TxContext> [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+93
procedure {:inline 1} $0_prover_val'$2_tx_context_TxContext'$aborts(_$t0: $2_tx_context_TxContext) returns (res: bool)
{
    // declare local variables
    var $t1: $2_tx_context_TxContext;
    var $t2: bool;
    var $t3: int;
    var $t4: $2_tx_context_TxContext;
    var $t5: bool;
    var $t6: bool;
    var $t0: $2_tx_context_TxContext;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // $t2 := prover::type_inv<#0>($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:28:1+1
    assume {:print "$at(4,513,514)"} true;
    $t2 := true;

    // $t5 := ==($t4, $t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:31:20+2
    assume {:print "$at(4,586,588)"} true;
    $t5 := $IsEqual'$2_tx_context_TxContext'($t4, $t0);

    // $t6 := prover::type_inv<#0>($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $t6 := true;

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
L1:

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
L2:

    // abort($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:34:1+1
    assume {:print "$at(4,605,606)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct table_vec::TableVec<vector<u8>> at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui_git_next/crates/sui-framework/packages/sui-framework/sources/table_vec.move:9:1+137
datatype $2_table_vec_TableVec'vec'u8'' {
    $2_table_vec_TableVec'vec'u8''($contents: $2_table_Table'u64_vec'u8'')
}
function {:inline} $Update'$2_table_vec_TableVec'vec'u8'''_contents(s: $2_table_vec_TableVec'vec'u8'', x: $2_table_Table'u64_vec'u8''): $2_table_vec_TableVec'vec'u8'' {
    $2_table_vec_TableVec'vec'u8''(x)
}
function {:inline} $IsEqual'$2_table_vec_TableVec'vec'u8'''(s1: $2_table_vec_TableVec'vec'u8'', s2: $2_table_vec_TableVec'vec'u8''): bool {
    s1 == s2
}
procedure {:inline 1} $0_prover_type_inv'$2_table_vec_TableVec'vec'u8'''(s: $2_table_vec_TableVec'vec'u8'') returns (res: bool) {
    res := true;
    return;
}

// struct validator_metadata::ValidatorMetadata at ./../ika_system/sources/staking/validator_metadata.move:13:1+172
datatype $0_validator_metadata_ValidatorMetadata {
    $0_validator_metadata_ValidatorMetadata($image_url: $1_string_String, $project_url: $1_string_String, $description: $1_string_String, $extra_fields: $2_vec_map_VecMap'$1_string_String_$1_string_String')
}
function {:inline} $Update'$0_validator_metadata_ValidatorMetadata'_image_url(s: $0_validator_metadata_ValidatorMetadata, x: $1_string_String): $0_validator_metadata_ValidatorMetadata {
    $0_validator_metadata_ValidatorMetadata(x, s->$project_url, s->$description, s->$extra_fields)
}
function {:inline} $Update'$0_validator_metadata_ValidatorMetadata'_project_url(s: $0_validator_metadata_ValidatorMetadata, x: $1_string_String): $0_validator_metadata_ValidatorMetadata {
    $0_validator_metadata_ValidatorMetadata(s->$image_url, x, s->$description, s->$extra_fields)
}
function {:inline} $Update'$0_validator_metadata_ValidatorMetadata'_description(s: $0_validator_metadata_ValidatorMetadata, x: $1_string_String): $0_validator_metadata_ValidatorMetadata {
    $0_validator_metadata_ValidatorMetadata(s->$image_url, s->$project_url, x, s->$extra_fields)
}
function {:inline} $Update'$0_validator_metadata_ValidatorMetadata'_extra_fields(s: $0_validator_metadata_ValidatorMetadata, x: $2_vec_map_VecMap'$1_string_String_$1_string_String'): $0_validator_metadata_ValidatorMetadata {
    $0_validator_metadata_ValidatorMetadata(s->$image_url, s->$project_url, s->$description, x)
}
function $IsValid'$0_validator_metadata_ValidatorMetadata'(s: $0_validator_metadata_ValidatorMetadata): bool {
    $IsValid'$1_string_String'(s->$image_url)
      && $IsValid'$1_string_String'(s->$project_url)
      && $IsValid'$1_string_String'(s->$description)
      && $IsValid'$2_vec_map_VecMap'$1_string_String_$1_string_String''(s->$extra_fields)
}
function {:inline} $IsEqual'$0_validator_metadata_ValidatorMetadata'(s1: $0_validator_metadata_ValidatorMetadata, s2: $0_validator_metadata_ValidatorMetadata): bool {
    $IsEqual'$1_string_String'(s1->$image_url, s2->$image_url)
    && $IsEqual'$1_string_String'(s1->$project_url, s2->$project_url)
    && $IsEqual'$1_string_String'(s1->$description, s2->$description)
    && $IsEqual'$2_vec_map_VecMap'$1_string_String_$1_string_String''(s1->$extra_fields, s2->$extra_fields)}
procedure {:inline 1} $0_prover_type_inv'$0_validator_metadata_ValidatorMetadata'(s: $0_validator_metadata_ValidatorMetadata) returns (res: bool) {
    res := true;
    return;
}

// struct validator_info::ValidatorInfo at ./../ika_system/sources/staking/validator_info.move:56:1+2002
datatype $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo($name: $1_string_String, $validator_id: $2_object_ID, $network_address: $1_string_String, $p2p_address: $1_string_String, $consensus_address: $1_string_String, $protocol_pubkey_bytes: Vec (int), $protocol_pubkey: $2_group_ops_Element'$2_bls12381_UncompressedG1', $network_pubkey_bytes: Vec (int), $consensus_pubkey_bytes: Vec (int), $mpc_data_bytes: $1_option_Option'$2_table_vec_TableVec'vec'u8''', $next_epoch_protocol_pubkey_bytes: $1_option_Option'vec'u8'', $next_epoch_network_pubkey_bytes: $1_option_Option'vec'u8'', $next_epoch_consensus_pubkey_bytes: $1_option_Option'vec'u8'', $next_epoch_mpc_data_bytes: $1_option_Option'$2_table_vec_TableVec'vec'u8''', $next_epoch_network_address: $1_option_Option'$1_string_String', $next_epoch_p2p_address: $1_option_Option'$1_string_String', $next_epoch_consensus_address: $1_option_Option'$1_string_String', $previous_mpc_data_bytes: $1_option_Option'$2_table_vec_TableVec'vec'u8''', $metadata: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata')
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_name(s: $0_validator_info_ValidatorInfo, x: $1_string_String): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(x, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_validator_id(s: $0_validator_info_ValidatorInfo, x: $2_object_ID): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, x, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_network_address(s: $0_validator_info_ValidatorInfo, x: $1_string_String): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, x, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_p2p_address(s: $0_validator_info_ValidatorInfo, x: $1_string_String): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, x, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_consensus_address(s: $0_validator_info_ValidatorInfo, x: $1_string_String): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, x, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_protocol_pubkey_bytes(s: $0_validator_info_ValidatorInfo, x: Vec (int)): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, x, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_protocol_pubkey(s: $0_validator_info_ValidatorInfo, x: $2_group_ops_Element'$2_bls12381_UncompressedG1'): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, x, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_network_pubkey_bytes(s: $0_validator_info_ValidatorInfo, x: Vec (int)): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, x, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_consensus_pubkey_bytes(s: $0_validator_info_ValidatorInfo, x: Vec (int)): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, x, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_mpc_data_bytes(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'$2_table_vec_TableVec'vec'u8'''): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, x, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_protocol_pubkey_bytes(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'vec'u8''): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, x, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_network_pubkey_bytes(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'vec'u8''): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, x, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_consensus_pubkey_bytes(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'vec'u8''): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, x, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_mpc_data_bytes(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'$2_table_vec_TableVec'vec'u8'''): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, x, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_network_address(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'$1_string_String'): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, x, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_p2p_address(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'$1_string_String'): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, x, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_next_epoch_consensus_address(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'$1_string_String'): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, x, s->$previous_mpc_data_bytes, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_previous_mpc_data_bytes(s: $0_validator_info_ValidatorInfo, x: $1_option_Option'$2_table_vec_TableVec'vec'u8'''): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, x, s->$metadata)
}
function {:inline} $Update'$0_validator_info_ValidatorInfo'_metadata(s: $0_validator_info_ValidatorInfo, x: $0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata'): $0_validator_info_ValidatorInfo {
    $0_validator_info_ValidatorInfo(s->$name, s->$validator_id, s->$network_address, s->$p2p_address, s->$consensus_address, s->$protocol_pubkey_bytes, s->$protocol_pubkey, s->$network_pubkey_bytes, s->$consensus_pubkey_bytes, s->$mpc_data_bytes, s->$next_epoch_protocol_pubkey_bytes, s->$next_epoch_network_pubkey_bytes, s->$next_epoch_consensus_pubkey_bytes, s->$next_epoch_mpc_data_bytes, s->$next_epoch_network_address, s->$next_epoch_p2p_address, s->$next_epoch_consensus_address, s->$previous_mpc_data_bytes, x)
}
function $IsValid'$0_validator_info_ValidatorInfo'(s: $0_validator_info_ValidatorInfo): bool {
    $IsValid'$1_string_String'(s->$name)
      && $IsValid'$2_object_ID'(s->$validator_id)
      && $IsValid'$1_string_String'(s->$network_address)
      && $IsValid'$1_string_String'(s->$p2p_address)
      && $IsValid'$1_string_String'(s->$consensus_address)
      && $IsValid'vec'u8''(s->$protocol_pubkey_bytes)
      && $IsValid'$2_group_ops_Element'$2_bls12381_UncompressedG1''(s->$protocol_pubkey)
      && $IsValid'vec'u8''(s->$network_pubkey_bytes)
      && $IsValid'vec'u8''(s->$consensus_pubkey_bytes)
      && $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s->$mpc_data_bytes)
      && $IsValid'$1_option_Option'vec'u8'''(s->$next_epoch_protocol_pubkey_bytes)
      && $IsValid'$1_option_Option'vec'u8'''(s->$next_epoch_network_pubkey_bytes)
      && $IsValid'$1_option_Option'vec'u8'''(s->$next_epoch_consensus_pubkey_bytes)
      && $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s->$next_epoch_mpc_data_bytes)
      && $IsValid'$1_option_Option'$1_string_String''(s->$next_epoch_network_address)
      && $IsValid'$1_option_Option'$1_string_String''(s->$next_epoch_p2p_address)
      && $IsValid'$1_option_Option'$1_string_String''(s->$next_epoch_consensus_address)
      && $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s->$previous_mpc_data_bytes)
      && $IsValid'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''(s->$metadata)
}
function {:inline} $IsEqual'$0_validator_info_ValidatorInfo'(s1: $0_validator_info_ValidatorInfo, s2: $0_validator_info_ValidatorInfo): bool {
    $IsEqual'$1_string_String'(s1->$name, s2->$name)
    && $IsEqual'$2_object_ID'(s1->$validator_id, s2->$validator_id)
    && $IsEqual'$1_string_String'(s1->$network_address, s2->$network_address)
    && $IsEqual'$1_string_String'(s1->$p2p_address, s2->$p2p_address)
    && $IsEqual'$1_string_String'(s1->$consensus_address, s2->$consensus_address)
    && $IsEqual'vec'u8''(s1->$protocol_pubkey_bytes, s2->$protocol_pubkey_bytes)
    && $IsEqual'$2_group_ops_Element'$2_bls12381_UncompressedG1''(s1->$protocol_pubkey, s2->$protocol_pubkey)
    && $IsEqual'vec'u8''(s1->$network_pubkey_bytes, s2->$network_pubkey_bytes)
    && $IsEqual'vec'u8''(s1->$consensus_pubkey_bytes, s2->$consensus_pubkey_bytes)
    && $IsEqual'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s1->$mpc_data_bytes, s2->$mpc_data_bytes)
    && $IsEqual'$1_option_Option'vec'u8'''(s1->$next_epoch_protocol_pubkey_bytes, s2->$next_epoch_protocol_pubkey_bytes)
    && $IsEqual'$1_option_Option'vec'u8'''(s1->$next_epoch_network_pubkey_bytes, s2->$next_epoch_network_pubkey_bytes)
    && $IsEqual'$1_option_Option'vec'u8'''(s1->$next_epoch_consensus_pubkey_bytes, s2->$next_epoch_consensus_pubkey_bytes)
    && $IsEqual'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s1->$next_epoch_mpc_data_bytes, s2->$next_epoch_mpc_data_bytes)
    && $IsEqual'$1_option_Option'$1_string_String''(s1->$next_epoch_network_address, s2->$next_epoch_network_address)
    && $IsEqual'$1_option_Option'$1_string_String''(s1->$next_epoch_p2p_address, s2->$next_epoch_p2p_address)
    && $IsEqual'$1_option_Option'$1_string_String''(s1->$next_epoch_consensus_address, s2->$next_epoch_consensus_address)
    && $IsEqual'$1_option_Option'$2_table_vec_TableVec'vec'u8''''(s1->$previous_mpc_data_bytes, s2->$previous_mpc_data_bytes)
    && $IsEqual'$0_extended_field_ExtendedField'$0_validator_metadata_ValidatorMetadata''(s1->$metadata, s2->$metadata)}
procedure {:inline 1} $0_prover_type_inv'$0_validator_info_ValidatorInfo'(s: $0_validator_info_ValidatorInfo) returns (res: bool) {
    res := true;
    return;
}

// fun validator_info::validator_id [baseline] at ./../ika_system/sources/staking/validator_info.move:507:1+75
procedure {:inline 1} $0_validator_info_validator_id$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:507:1+1
    assume {:print "$at(249,20332,20333)"} true;
    assume {:print "$track_local(140,18,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.validator_id($t0) at ./../ika_system/sources/staking/validator_info.move:508:5+17
    assume {:print "$at(249,20388,20405)"} true;
    $t1 := $t0->$validator_id;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:508:5+17
    assume {:print "$track_return(140,18,0,$2_object_ID):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:509:1+1
    assume {:print "$at(249,20406,20407)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:509:1+1
    assume {:print "$at(249,20406,20407)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::protocol_pubkey [baseline] at ./../ika_system/sources/staking/validator_info.move:532:1+104
procedure {:inline 1} $0_validator_info_protocol_pubkey$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $2_group_ops_Element'$2_bls12381_UncompressedG1')
{
    // declare local variables
    var $t1: $2_group_ops_Element'$2_bls12381_UncompressedG1';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$2_group_ops_Element'$2_bls12381_UncompressedG1'': $2_group_ops_Element'$2_bls12381_UncompressedG1';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:532:1+1
    assume {:print "$at(249,20957,20958)"} true;
    assume {:print "$track_local(140,23,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.protocol_pubkey($t0) at ./../ika_system/sources/staking/validator_info.move:533:5+21
    assume {:print "$at(249,21038,21059)"} true;
    $t1 := $t0->$protocol_pubkey;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:533:5+21
    assume {:print "$track_return(140,23,0,$2_group_ops_Element'$2_bls12381_UncompressedG1'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:534:1+1
    assume {:print "$at(249,21060,21061)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:534:1+1
    assume {:print "$at(249,21060,21061)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::consensus_address [baseline] at ./../ika_system/sources/staking/validator_info.move:522:1+91
procedure {:inline 1} $0_validator_info_consensus_address$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: $1_string_String;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_string_String': $1_string_String;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:522:1+1
    assume {:print "$at(249,20673,20674)"} true;
    assume {:print "$track_local(140,21,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.consensus_address($t0) at ./../ika_system/sources/staking/validator_info.move:523:5+23
    assume {:print "$at(249,20739,20762)"} true;
    $t1 := $t0->$consensus_address;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:523:5+23
    assume {:print "$track_return(140,21,0,$1_string_String):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:524:1+1
    assume {:print "$at(249,20763,20764)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:524:1+1
    assume {:print "$at(249,20763,20764)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::consensus_pubkey_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:542:1+105
procedure {:inline 1} $0_validator_info_consensus_pubkey_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:542:1+1
    assume {:print "$at(249,21250,21251)"} true;
    assume {:print "$track_local(140,25,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.consensus_pubkey_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:543:5+28
    assume {:print "$at(249,21325,21353)"} true;
    $t1 := $t0->$consensus_pubkey_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:543:5+28
    assume {:print "$track_return(140,25,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:544:1+1
    assume {:print "$at(249,21354,21355)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:544:1+1
    assume {:print "$at(249,21354,21355)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::mpc_data_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:547:1+107
procedure {:inline 1} $0_validator_info_mpc_data_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''')
{
    // declare local variables
    var $t1: $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$2_table_vec_TableVec'vec'u8'''': $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:547:1+1
    assume {:print "$at(249,21395,21396)"} true;
    assume {:print "$track_local(140,26,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.mpc_data_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:548:5+20
    assume {:print "$at(249,21480,21500)"} true;
    $t1 := $t0->$mpc_data_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:548:5+20
    assume {:print "$track_return(140,26,0,$1_option_Option'$2_table_vec_TableVec'vec'u8'''):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:549:1+1
    assume {:print "$at(249,21501,21502)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:549:1+1
    assume {:print "$at(249,21501,21502)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::network_address [baseline] at ./../ika_system/sources/staking/validator_info.move:512:1+87
procedure {:inline 1} $0_validator_info_network_address$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: $1_string_String;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_string_String': $1_string_String;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:512:1+1
    assume {:print "$at(249,20441,20442)"} true;
    assume {:print "$track_local(140,19,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.network_address($t0) at ./../ika_system/sources/staking/validator_info.move:513:5+21
    assume {:print "$at(249,20505,20526)"} true;
    $t1 := $t0->$network_address;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:513:5+21
    assume {:print "$track_return(140,19,0,$1_string_String):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:514:1+1
    assume {:print "$at(249,20527,20528)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:514:1+1
    assume {:print "$at(249,20527,20528)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::network_pubkey_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:537:1+101
procedure {:inline 1} $0_validator_info_network_pubkey_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:537:1+1
    assume {:print "$at(249,21104,21105)"} true;
    assume {:print "$track_local(140,24,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.network_pubkey_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:538:5+26
    assume {:print "$at(249,21177,21203)"} true;
    $t1 := $t0->$network_pubkey_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:538:5+26
    assume {:print "$track_return(140,24,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:539:1+1
    assume {:print "$at(249,21204,21205)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:539:1+1
    assume {:print "$at(249,21204,21205)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::protocol_pubkey_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:527:1+103
procedure {:inline 1} $0_validator_info_protocol_pubkey_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:527:1+1
    assume {:print "$at(249,20808,20809)"} true;
    assume {:print "$track_local(140,22,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.protocol_pubkey_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:528:5+27
    assume {:print "$at(249,20882,20909)"} true;
    $t1 := $t0->$protocol_pubkey_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:528:5+27
    assume {:print "$track_return(140,22,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:529:1+1
    assume {:print "$at(249,20910,20911)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:529:1+1
    assume {:print "$at(249,20910,20911)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::p2p_address [baseline] at ./../ika_system/sources/staking/validator_info.move:517:1+79
procedure {:inline 1} $0_validator_info_p2p_address$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: $1_string_String;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_string_String': $1_string_String;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:517:1+1
    assume {:print "$at(249,20558,20559)"} true;
    assume {:print "$track_local(140,20,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.p2p_address($t0) at ./../ika_system/sources/staking/validator_info.move:518:5+17
    assume {:print "$at(249,20618,20635)"} true;
    $t1 := $t0->$p2p_address;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:518:5+17
    assume {:print "$track_return(140,20,0,$1_string_String):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:519:1+1
    assume {:print "$at(249,20636,20637)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:519:1+1
    assume {:print "$at(249,20636,20637)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_consensus_address [baseline] at ./../ika_system/sources/staking/validator_info.move:562:1+121
procedure {:inline 1} $0_validator_info_next_epoch_consensus_address$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String')
{
    // declare local variables
    var $t1: $1_option_Option'$1_string_String';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$1_string_String'': $1_option_Option'$1_string_String';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:562:1+1
    assume {:print "$at(249,21861,21862)"} true;
    assume {:print "$track_local(140,29,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_consensus_address($t0) at ./../ika_system/sources/staking/validator_info.move:563:5+34
    assume {:print "$at(249,21946,21980)"} true;
    $t1 := $t0->$next_epoch_consensus_address;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:563:5+34
    assume {:print "$track_return(140,29,0,$1_option_Option'$1_string_String'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:564:1+1
    assume {:print "$at(249,21981,21982)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:564:1+1
    assume {:print "$at(249,21981,21982)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_consensus_pubkey_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:577:1+135
procedure {:inline 1} $0_validator_info_next_epoch_consensus_pubkey_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'')
{
    // declare local variables
    var $t1: $1_option_Option'vec'u8'';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'vec'u8''': $1_option_Option'vec'u8'';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:577:1+1
    assume {:print "$at(249,22411,22412)"} true;
    assume {:print "$track_local(140,32,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_consensus_pubkey_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:578:5+39
    assume {:print "$at(249,22505,22544)"} true;
    $t1 := $t0->$next_epoch_consensus_pubkey_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:578:5+39
    assume {:print "$track_return(140,32,0,$1_option_Option'vec'u8''):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:579:1+1
    assume {:print "$at(249,22545,22546)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:579:1+1
    assume {:print "$at(249,22545,22546)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_mpc_data_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:582:1+136
procedure {:inline 1} $0_validator_info_next_epoch_mpc_data_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''')
{
    // declare local variables
    var $t1: $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$2_table_vec_TableVec'vec'u8'''': $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:582:1+1
    assume {:print "$at(249,22591,22592)"} true;
    assume {:print "$track_local(140,33,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_mpc_data_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:585:5+31
    assume {:print "$at(249,22694,22725)"} true;
    $t1 := $t0->$next_epoch_mpc_data_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:585:5+31
    assume {:print "$track_return(140,33,0,$1_option_Option'$2_table_vec_TableVec'vec'u8'''):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:586:1+1
    assume {:print "$at(249,22726,22727)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:586:1+1
    assume {:print "$at(249,22726,22727)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_network_address [baseline] at ./../ika_system/sources/staking/validator_info.move:552:1+117
procedure {:inline 1} $0_validator_info_next_epoch_network_address$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String')
{
    // declare local variables
    var $t1: $1_option_Option'$1_string_String';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$1_string_String'': $1_option_Option'$1_string_String';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:552:1+1
    assume {:print "$at(249,21547,21548)"} true;
    assume {:print "$track_local(140,27,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_network_address($t0) at ./../ika_system/sources/staking/validator_info.move:553:5+32
    assume {:print "$at(249,21630,21662)"} true;
    $t1 := $t0->$next_epoch_network_address;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:553:5+32
    assume {:print "$track_return(140,27,0,$1_option_Option'$1_string_String'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:554:1+1
    assume {:print "$at(249,21663,21664)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:554:1+1
    assume {:print "$at(249,21663,21664)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_network_pubkey_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:572:1+131
procedure {:inline 1} $0_validator_info_next_epoch_network_pubkey_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'')
{
    // declare local variables
    var $t1: $1_option_Option'vec'u8'';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'vec'u8''': $1_option_Option'vec'u8'';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:572:1+1
    assume {:print "$at(249,22224,22225)"} true;
    assume {:print "$track_local(140,31,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_network_pubkey_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:573:5+37
    assume {:print "$at(249,22316,22353)"} true;
    $t1 := $t0->$next_epoch_network_pubkey_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:573:5+37
    assume {:print "$track_return(140,31,0,$1_option_Option'vec'u8''):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:574:1+1
    assume {:print "$at(249,22354,22355)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:574:1+1
    assume {:print "$at(249,22354,22355)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_p2p_address [baseline] at ./../ika_system/sources/staking/validator_info.move:557:1+109
procedure {:inline 1} $0_validator_info_next_epoch_p2p_address$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String')
{
    // declare local variables
    var $t1: $1_option_Option'$1_string_String';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$1_string_String'': $1_option_Option'$1_string_String';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:557:1+1
    assume {:print "$at(249,21705,21706)"} true;
    assume {:print "$track_local(140,28,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_p2p_address($t0) at ./../ika_system/sources/staking/validator_info.move:558:5+28
    assume {:print "$at(249,21784,21812)"} true;
    $t1 := $t0->$next_epoch_p2p_address;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:558:5+28
    assume {:print "$track_return(140,28,0,$1_option_Option'$1_string_String'):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:559:1+1
    assume {:print "$at(249,21813,21814)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:559:1+1
    assume {:print "$at(249,21813,21814)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::next_epoch_protocol_pubkey_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:567:1+133
procedure {:inline 1} $0_validator_info_next_epoch_protocol_pubkey_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'')
{
    // declare local variables
    var $t1: $1_option_Option'vec'u8'';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'vec'u8''': $1_option_Option'vec'u8'';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:567:1+1
    assume {:print "$at(249,22037,22038)"} true;
    assume {:print "$track_local(140,30,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.next_epoch_protocol_pubkey_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:568:5+38
    assume {:print "$at(249,22130,22168)"} true;
    $t1 := $t0->$next_epoch_protocol_pubkey_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:568:5+38
    assume {:print "$track_return(140,30,0,$1_option_Option'vec'u8''):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:569:1+1
    assume {:print "$at(249,22169,22170)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:569:1+1
    assume {:print "$at(249,22169,22170)"} true;
    $ret0 := $t1;
    return;

}

// fun validator_info::previous_mpc_data_bytes [baseline] at ./../ika_system/sources/staking/validator_info.move:590:1+132
procedure {:inline 1} $0_validator_info_previous_mpc_data_bytes$impl(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''')
{
    // declare local variables
    var $t1: $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$2_table_vec_TableVec'vec'u8'''': $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../ika_system/sources/staking/validator_info.move:590:1+1
    assume {:print "$at(249,22771,22772)"} true;
    assume {:print "$track_local(140,34,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := get_field<validator_info::ValidatorInfo>.previous_mpc_data_bytes($t0) at ./../ika_system/sources/staking/validator_info.move:593:5+29
    assume {:print "$at(249,22872,22901)"} true;
    $t1 := $t0->$previous_mpc_data_bytes;

    // trace_return[0]($t1) at ./../ika_system/sources/staking/validator_info.move:593:5+29
    assume {:print "$track_return(140,34,0,$1_option_Option'$2_table_vec_TableVec'vec'u8'''):", $t1} $t1 == $t1;

    // label L1 at ./../ika_system/sources/staking/validator_info.move:594:1+1
    assume {:print "$at(249,22902,22903)"} true;
L1:

    // return $t1 at ./../ika_system/sources/staking/validator_info.move:594:1+1
    assume {:print "$at(249,22902,22903)"} true;
    $ret0 := $t1;
    return;

}

// fun object_spec::delete_impl_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:6:1+59
datatype $2_object_delete_impl_opaque_return_type {
    $2_object_delete_impl_opaque_return_type()
}

function $2_object_delete_impl$opaque(_$t0: int) returns ($ret: $2_object_delete_impl_opaque_return_type);

procedure {:inline 1} $2_object_delete_impl(_$t0: int) returns ()
{
    // declare local variables
    var $t1: int;
    var $t0: int;
    var $temp_opaque_res_var: $2_object_delete_impl_opaque_return_type;
    var $temp_0'address': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[id]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:6:1+1
    assume {:print "$at(29,125,126)"} true;
    assume {:print "$track_local(161,0,0,address):", $t0} $t0 == $t0;

    // object::delete_impl($t0) on_abort goto L2 with $t1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:7:5+15
    assume {:print "$at(29,166,181)"} true;
    $temp_opaque_res_var := $2_object_delete_impl$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(29,166,181)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(161,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:8:1+1
    assume {:print "$at(29,183,184)"} true;
L1:

    // return () at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:8:1+1
    assume {:print "$at(29,183,184)"} true;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:8:1+1
L2:

    // abort($t1) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/object.move:8:1+1
    assume {:print "$at(29,183,184)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::activation_epoch_spec [baseline] at ./sources/staked_ika_specs.move:16:1+94
function $0_staked_ika_activation_epoch$opaque(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int);

procedure {:inline 1} $0_staked_ika_activation_epoch(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:16:1+1
    assume {:print "$at(255,431,432)"} true;
    assume {:print "$track_local(167,2,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::activation_epoch($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:17:5+32
    assume {:print "$at(255,491,523)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_activation_epoch$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,491,523)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:16:1+94
    assume {:print "$at(255,431,525)"} true;
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:17:5+32
    assume {:print "$at(255,491,523)"} true;
    assume {:print "$track_return(167,2,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:18:1+1
    assume {:print "$at(255,524,525)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:18:1+1
    assume {:print "$at(255,524,525)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:18:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:18:1+1
    assume {:print "$at(255,524,525)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::is_staked_spec [baseline] at ./sources/staked_ika_specs.move:21:1+81
function $0_staked_ika_is_staked$opaque(_$t0: $0_staked_ika_StakedIka) returns ($ret0: bool);

procedure {:inline 1} $0_staked_ika_is_staked(_$t0: $0_staked_ika_StakedIka) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'bool': bool;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:21:1+1
    assume {:print "$at(255,588,589)"} true;
    assume {:print "$track_local(167,3,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::is_staked($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:22:5+25
    assume {:print "$at(255,642,667)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_is_staked$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,642,667)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,3):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:21:1+81
    assume {:print "$at(255,588,669)"} true;
    assume $IsValid'bool'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:22:5+25
    assume {:print "$at(255,642,667)"} true;
    assume {:print "$track_return(167,3,0,bool):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:23:1+1
    assume {:print "$at(255,668,669)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:23:1+1
    assume {:print "$at(255,668,669)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:23:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:23:1+1
    assume {:print "$at(255,668,669)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::is_withdrawing_spec [baseline] at ./sources/staked_ika_specs.move:26:1+91
function $0_staked_ika_is_withdrawing$opaque(_$t0: $0_staked_ika_StakedIka) returns ($ret0: bool);

procedure {:inline 1} $0_staked_ika_is_withdrawing(_$t0: $0_staked_ika_StakedIka) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'bool': bool;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:26:1+1
    assume {:print "$at(255,737,738)"} true;
    assume {:print "$track_local(167,4,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::is_withdrawing($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:27:5+30
    assume {:print "$at(255,796,826)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_is_withdrawing$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,796,826)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:26:1+91
    assume {:print "$at(255,737,828)"} true;
    assume $IsValid'bool'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:27:5+30
    assume {:print "$at(255,796,826)"} true;
    assume {:print "$track_return(167,4,0,bool):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:28:1+1
    assume {:print "$at(255,827,828)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:28:1+1
    assume {:print "$at(255,827,828)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:28:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:28:1+1
    assume {:print "$at(255,827,828)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::join_spec [baseline] at ./sources/staked_ika_specs.move:36:1+94
function $0_staked_ika_join$opaque(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: $0_staked_ika_StakedIka) returns ($ret0: $Mutation ($0_staked_ika_StakedIka));

procedure {:inline 1} $0_staked_ika_join(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: $0_staked_ika_StakedIka) returns ($ret0: $Mutation ($0_staked_ika_StakedIka))
{
    // declare local variables
    var $t2: int;
    var $t0: $Mutation ($0_staked_ika_StakedIka);
    var $t1: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:36:1+1
    assume {:print "$at(255,1044,1045)"} true;
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(167,6,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // trace_local[other]($t1) at ./sources/staked_ika_specs.move:36:1+1
    assume {:print "$track_local(167,6,1,$0_staked_ika_StakedIka):", $t1} $t1 == $t1;

    // staked_ika::join($t0, $t1) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:37:5+27
    assume {:print "$at(255,1109,1136)"} true;
    havoc $abort_flag;
    $t0 := $0_staked_ika_join$opaque($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(255,1109,1136)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,6):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t0) at ./sources/staked_ika_specs.move:36:1+94
    assume {:print "$at(255,1044,1138)"} true;
    assume $IsValid'$0_staked_ika_StakedIka'($Dereference($t0));

    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:37:5+27
    assume {:print "$at(255,1109,1136)"} true;
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(167,6,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // label L1 at ./sources/staked_ika_specs.move:38:1+1
    assume {:print "$at(255,1137,1138)"} true;
L1:

    // return () at ./sources/staked_ika_specs.move:38:1+1
    assume {:print "$at(255,1137,1138)"} true;
    $ret0 := $t0;
    return;

    // label L2 at ./sources/staked_ika_specs.move:38:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:38:1+1
    assume {:print "$at(255,1137,1138)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::join_spec [baseline] at ./sources/staked_ika_specs.move:36:1+94
procedure {:inline 1} $0_staked_ika_join$aborts(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: $0_staked_ika_StakedIka) returns (res: bool)
{
    // declare local variables
    var $t2: int;
    var $t0: $Mutation ($0_staked_ika_StakedIka);
    var $t1: $0_staked_ika_StakedIka;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;
    res := true;

    // bytecode translation starts here
    // label L1 at ./sources/staked_ika_specs.move:38:1+1
    assume {:print "$at(255,1137,1138)"} true;
L1:

    // label L2 at ./sources/staked_ika_specs.move:38:1+1
    assume {:print "$at(255,1137,1138)"} true;
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:38:1+1
    assume {:print "$at(255,1137,1138)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::split_spec [baseline] at ./sources/staked_ika_specs.move:41:1+122
procedure $0_staked_ika_split$opaque(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $0_staked_ika_StakedIka, $ret1: $Mutation ($0_staked_ika_StakedIka), $ret2: $Mutation ($2_tx_context_TxContext));

procedure {:inline 1} $0_staked_ika_split(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $0_staked_ika_StakedIka, $ret1: $Mutation ($0_staked_ika_StakedIka), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: $0_staked_ika_StakedIka;
    var $t4: int;
    var $t0: $Mutation ($0_staked_ika_StakedIka);
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:41:1+1
    assume {:print "$at(255,1197,1198)"} true;
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(167,7,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // trace_local[amount]($t1) at ./sources/staked_ika_specs.move:41:1+1
    assume {:print "$track_local(167,7,1,u64):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/staked_ika_specs.move:41:1+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(167,7,2,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := staked_ika::split($t0, $t1, $t2) on_abort goto L2 with $t4 at ./sources/staked_ika_specs.move:42:5+34
    assume {:print "$at(255,1283,1317)"} true;
    havoc $abort_flag;
    call $t3,$t0,$t2 := $0_staked_ika_split$opaque($t0, $t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(255,1283,1317)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(167,7):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t3 := havoc[val]() at ./sources/staked_ika_specs.move:41:1+122
    assume {:print "$at(255,1197,1319)"} true;
    havoc $t3;

    // assume WellFormed($t3) at ./sources/staked_ika_specs.move:41:1+122
    assume $IsValid'$0_staked_ika_StakedIka'($t3);

    // $t0 := havoc[mut]() at ./sources/staked_ika_specs.move:41:1+122
    havoc $temp_0'$0_staked_ika_StakedIka';
    $t0 := $UpdateMutation($t0, $temp_0'$0_staked_ika_StakedIka');

    // assume WellFormed($t0) at ./sources/staked_ika_specs.move:41:1+122
    assume $IsValid'$0_staked_ika_StakedIka'($Dereference($t0));

    // $t2 := havoc[mut]() at ./sources/staked_ika_specs.move:41:1+122
    havoc $temp_0'$2_tx_context_TxContext';
    $t2 := $UpdateMutation($t2, $temp_0'$2_tx_context_TxContext');

    // assume WellFormed($t2) at ./sources/staked_ika_specs.move:41:1+122
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t2));

    // trace_return[0]($t3) at ./sources/staked_ika_specs.move:42:5+34
    assume {:print "$at(255,1283,1317)"} true;
    assume {:print "$track_return(167,7,0,$0_staked_ika_StakedIka):", $t3} $t3 == $t3;

    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:42:5+34
    $temp_0'$0_staked_ika_StakedIka' := $Dereference($t0);
    assume {:print "$track_local(167,7,0,$0_staked_ika_StakedIka):", $temp_0'$0_staked_ika_StakedIka'} $temp_0'$0_staked_ika_StakedIka' == $temp_0'$0_staked_ika_StakedIka';

    // trace_local[ctx]($t2) at ./sources/staked_ika_specs.move:42:5+34
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(167,7,2,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/staked_ika_specs.move:43:1+1
    assume {:print "$at(255,1318,1319)"} true;
L1:

    // return $t3 at ./sources/staked_ika_specs.move:43:1+1
    assume {:print "$at(255,1318,1319)"} true;
    $ret0 := $t3;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at ./sources/staked_ika_specs.move:43:1+1
L2:

    // abort($t4) at ./sources/staked_ika_specs.move:43:1+1
    assume {:print "$at(255,1318,1319)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::split_spec [baseline] at ./sources/staked_ika_specs.move:41:1+122
procedure {:inline 1} $0_staked_ika_split$aborts(_$t0: $Mutation ($0_staked_ika_StakedIka), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns (res: bool)
{
    // declare local variables
    var $t3: $0_staked_ika_StakedIka;
    var $t4: int;
    var $t0: $Mutation ($0_staked_ika_StakedIka);
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $abort_if_cond: bool;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    res := true;

    // bytecode translation starts here
    // label L1 at ./sources/staked_ika_specs.move:43:1+1
    assume {:print "$at(255,1318,1319)"} true;
L1:

    // label L2 at ./sources/staked_ika_specs.move:43:1+1
    assume {:print "$at(255,1318,1319)"} true;
L2:

    // abort($t4) at ./sources/staked_ika_specs.move:43:1+1
    assume {:print "$at(255,1318,1319)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::validator_id_spec [baseline] at ./sources/staked_ika_specs.move:6:1+85
function $0_staked_ika_validator_id$opaque(_$t0: $0_staked_ika_StakedIka) returns ($ret0: $2_object_ID);

procedure {:inline 1} $0_staked_ika_validator_id(_$t0: $0_staked_ika_StakedIka) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:6:1+1
    assume {:print "$at(255,145,146)"} true;
    assume {:print "$track_local(167,0,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::validator_id($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:7:5+28
    assume {:print "$at(255,200,228)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_validator_id$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,200,228)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:6:1+85
    assume {:print "$at(255,145,230)"} true;
    assume $IsValid'$2_object_ID'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:7:5+28
    assume {:print "$at(255,200,228)"} true;
    assume {:print "$track_return(167,0,0,$2_object_ID):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:8:1+1
    assume {:print "$at(255,229,230)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:8:1+1
    assume {:print "$at(255,229,230)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:8:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:8:1+1
    assume {:print "$at(255,229,230)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::value_spec [baseline] at ./sources/staked_ika_specs.move:11:1+72
function $0_staked_ika_value$opaque(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int);

procedure {:inline 1} $0_staked_ika_value(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:11:1+1
    assume {:print "$at(255,289,290)"} true;
    assume {:print "$track_local(167,1,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::value($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,338,359)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_value$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,338,359)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:11:1+72
    assume {:print "$at(255,289,361)"} true;
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,338,359)"} true;
    assume {:print "$track_return(167,1,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,360,361)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,360,361)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:13:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,360,361)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::withdraw_epoch_spec [baseline] at ./sources/staked_ika_specs.move:31:1+90
function $0_staked_ika_withdraw_epoch$opaque(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int);

procedure {:inline 1} $0_staked_ika_withdraw_epoch(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:31:1+1
    assume {:print "$at(255,896,897)"} true;
    assume {:print "$track_local(167,5,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::withdraw_epoch($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:32:5+30
    assume {:print "$at(255,954,984)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_withdraw_epoch$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,954,984)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,5):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:31:1+90
    assume {:print "$at(255,896,986)"} true;
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:32:5+30
    assume {:print "$at(255,954,984)"} true;
    assume {:print "$track_return(167,5,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,985,986)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,985,986)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:33:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,985,986)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::withdraw_epoch_spec [baseline] at ./sources/staked_ika_specs.move:31:1+90
procedure {:inline 1} $0_staked_ika_withdraw_epoch$aborts(_$t0: $0_staked_ika_StakedIka) returns (res: bool)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $abort_if_cond: bool;
    $t0 := _$t0;
    res := true;

    // bytecode translation starts here
    // label L1 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,985,986)"} true;
L1:

    // label L2 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,985,986)"} true;
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,985,986)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun tx_context_spec::fresh_object_address_spec [baseline] at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:26:1+366
procedure $2_tx_context_fresh_object_address$opaque(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext));

procedure {:inline 1} $2_tx_context_fresh_object_address(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: $2_tx_context_TxContext;
    var $t2: int;
    var $t3: $2_tx_context_TxContext;
    var $t4: $2_tx_context_TxContext;
    var $t5: int;
    var $t6: $2_tx_context_TxContext;
    var $t7: int;
    var $t8: $2_tx_context_TxContext;
    var $t9: Vec (int);
    var $t10: Vec (int);
    var $t11: bool;
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'address': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:26:1+1
    assume {:print "$at(32,487,488)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(170,0,0,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := read_ref($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:27:24+3
    assume {:print "$at(32,572,575)"} true;
    $t3 := $Dereference($t0);

    // $t4 := prover::val<tx_context::TxContext>($t3) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:59:9+7
    assume {:print "$at(4,964,971)"} true;
    call $t4 := $0_prover_val'$2_tx_context_TxContext'($t3);

    // $t6 := prover::ref<tx_context::TxContext>($t4) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/prover/sources/prover.move:59:5+12
    assume {:print "$at(4,960,972)"} true;
    call $t6 := $0_prover_ref'$2_tx_context_TxContext'($t4);

    // trace_local[old_ctx#1#0]($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:27:9+7
    assume {:print "$at(32,557,564)"} true;
    assume {:print "$track_local(170,0,1,$2_tx_context_TxContext):", $t6} $t6 == $t6;

    // $t7 := tx_context::fresh_object_address($t0) on_abort goto L2 with $t5 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:28:18+25
    assume {:print "$at(32,595,620)"} true;
    call $t7,$t0 := $2_tx_context_fresh_object_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(32,595,620)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(170,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t7 := havoc[val]() at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:26:1+366
    assume {:print "$at(32,487,853)"} true;
    havoc $t7;

    // assume WellFormed($t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:26:1+366
    assume $IsValid'address'($t7);

    // $t0 := havoc[mut]() at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:26:1+366
    havoc $temp_0'$2_tx_context_TxContext';
    $t0 := $UpdateMutation($t0, $temp_0'$2_tx_context_TxContext');

    // assume WellFormed($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:26:1+366
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t0));

    // trace_local[result#1#0]($t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:28:9+6
    assume {:print "$at(32,586,592)"} true;
    assume {:print "$track_local(170,0,2,address):", $t7} $t7 == $t7;

    // $t8 := read_ref($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:30:13+3
    assume {:print "$at(32,684,687)"} true;
    $t8 := $Dereference($t0);

    // $t9 := tx_context::digest($t8) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:30:13+12
    call $t9 := $2_tx_context_digest($t8);

    // $t10 := tx_context::digest($t6) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:30:29+16
    assume {:print "$at(32,700,716)"} true;
    call $t10 := $2_tx_context_digest($t6);

    // $t11 := ==($t9, $t10) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:30:26+2
    assume {:print "$at(32,697,699)"} true;
    $t11 := $IsEqual'vec'u8''($t9, $t10);

    // prover::requires($t11) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:30:5+41
    call $0_prover_requires($t11);

    // trace_return[0]($t7) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:33:5+6
    assume {:print "$at(32,845,851)"} true;
    assume {:print "$track_return(170,0,0,address):", $t7} $t7 == $t7;

    // trace_local[ctx]($t0) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:33:5+6
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(170,0,0,$2_tx_context_TxContext):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:34:1+1
    assume {:print "$at(32,852,853)"} true;
L1:

    // return $t7 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:34:1+1
    assume {:print "$at(32,852,853)"} true;
    $ret0 := $t7;
    $ret1 := $t0;
    return;

    // label L2 at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:34:1+1
L2:

    // abort($t5) at /Users/danylo.provilskyi/.move/https___github_com_asymptotic-code_sui-prover_git_main/packages/sui-specs/sources/sui-framework/tx_context.move:34:1+1
    assume {:print "$at(32,852,853)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::validator_id_spec [baseline] at ./sources/validator_info_specs.move:12:1+90
function $0_validator_info_validator_id$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $2_object_ID);

procedure {:inline 1} $0_validator_info_validator_id(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:12:1+1
    assume {:print "$at(256,315,316)"} true;
    assume {:print "$track_local(173,0,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::validator_id($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:13:5+34
    assume {:print "$at(256,369,403)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_validator_id$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,369,403)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:12:1+90
    assume {:print "$at(256,315,405)"} true;
    assume $IsValid'$2_object_ID'($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:13:5+34
    assume {:print "$at(256,369,403)"} true;
    assume {:print "$track_return(173,0,0,$2_object_ID):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:14:1+1
    assume {:print "$at(256,404,405)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:14:1+1
    assume {:print "$at(256,404,405)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:14:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:14:1+1
    assume {:print "$at(256,404,405)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::consensus_address_spec [baseline] at ./sources/validator_info_specs.move:27:1+105
function $0_validator_info_consensus_address$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String);

procedure {:inline 1} $0_validator_info_consensus_address(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_string_String': $1_string_String;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:27:1+1
    assume {:print "$at(256,816,817)"} true;
    assume {:print "$track_local(173,3,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::consensus_address($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:28:5+39
    assume {:print "$at(256,880,919)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_consensus_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,880,919)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,3):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:27:1+105
    assume {:print "$at(256,816,921)"} true;
    assume $IsValid'$1_string_String'($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:28:5+39
    assume {:print "$at(256,880,919)"} true;
    assume {:print "$track_return(173,3,0,$1_string_String):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:29:1+1
    assume {:print "$at(256,920,921)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:29:1+1
    assume {:print "$at(256,920,921)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:29:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:29:1+1
    assume {:print "$at(256,920,921)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::consensus_pubkey_bytes_spec [baseline] at ./sources/validator_info_specs.move:47:1+119
function $0_validator_info_consensus_pubkey_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int));

procedure {:inline 1} $0_validator_info_consensus_pubkey_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:47:1+1
    assume {:print "$at(256,1581,1582)"} true;
    assume {:print "$track_local(173,7,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::consensus_pubkey_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:48:5+44
    assume {:print "$at(256,1654,1698)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_consensus_pubkey_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,1654,1698)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,7):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:47:1+119
    assume {:print "$at(256,1581,1700)"} true;
    assume $IsValid'vec'u8''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:48:5+44
    assume {:print "$at(256,1654,1698)"} true;
    assume {:print "$track_return(173,7,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:49:1+1
    assume {:print "$at(256,1699,1700)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:49:1+1
    assume {:print "$at(256,1699,1700)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:49:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:49:1+1
    assume {:print "$at(256,1699,1700)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::mpc_data_bytes_spec [baseline] at ./sources/validator_info_specs.move:52:1+121
function $0_validator_info_mpc_data_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''');

procedure {:inline 1} $0_validator_info_mpc_data_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''')
{
    // declare local variables
    var $t1: $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$2_table_vec_TableVec'vec'u8'''': $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:52:1+1
    assume {:print "$at(256,1772,1773)"} true;
    assume {:print "$track_local(173,8,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::mpc_data_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:53:5+36
    assume {:print "$at(256,1855,1891)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_mpc_data_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,1855,1891)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,8):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:52:1+121
    assume {:print "$at(256,1772,1893)"} true;
    assume $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:53:5+36
    assume {:print "$at(256,1855,1891)"} true;
    assume {:print "$track_return(173,8,0,$1_option_Option'$2_table_vec_TableVec'vec'u8'''):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:54:1+1
    assume {:print "$at(256,1892,1893)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:54:1+1
    assume {:print "$at(256,1892,1893)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:54:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:54:1+1
    assume {:print "$at(256,1892,1893)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::network_address_spec [baseline] at ./sources/validator_info_specs.move:17:1+101
function $0_validator_info_network_address$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String);

procedure {:inline 1} $0_validator_info_network_address(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_string_String': $1_string_String;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:17:1+1
    assume {:print "$at(256,478,479)"} true;
    assume {:print "$track_local(173,1,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::network_address($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:18:5+37
    assume {:print "$at(256,540,577)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_network_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,540,577)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:17:1+101
    assume {:print "$at(256,478,579)"} true;
    assume $IsValid'$1_string_String'($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:18:5+37
    assume {:print "$at(256,540,577)"} true;
    assume {:print "$track_return(173,1,0,$1_string_String):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:19:1+1
    assume {:print "$at(256,578,579)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:19:1+1
    assume {:print "$at(256,578,579)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:19:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:19:1+1
    assume {:print "$at(256,578,579)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::network_pubkey_bytes_spec [baseline] at ./sources/validator_info_specs.move:42:1+115
function $0_validator_info_network_pubkey_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int));

procedure {:inline 1} $0_validator_info_network_pubkey_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:42:1+1
    assume {:print "$at(256,1386,1387)"} true;
    assume {:print "$track_local(173,6,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::network_pubkey_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:43:5+42
    assume {:print "$at(256,1457,1499)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_network_pubkey_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,1457,1499)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,6):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:42:1+115
    assume {:print "$at(256,1386,1501)"} true;
    assume $IsValid'vec'u8''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:43:5+42
    assume {:print "$at(256,1457,1499)"} true;
    assume {:print "$track_return(173,6,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:44:1+1
    assume {:print "$at(256,1500,1501)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:44:1+1
    assume {:print "$at(256,1500,1501)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:44:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:44:1+1
    assume {:print "$at(256,1500,1501)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_consensus_address_spec [baseline] at ./sources/validator_info_specs.move:67:1+135
function $0_validator_info_next_epoch_consensus_address$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String');

procedure {:inline 1} $0_validator_info_next_epoch_consensus_address(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String')
{
    // declare local variables
    var $t1: $1_option_Option'$1_string_String';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$1_string_String'': $1_option_Option'$1_string_String';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:67:1+1
    assume {:print "$at(256,2397,2398)"} true;
    assume {:print "$track_local(173,11,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_consensus_address($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:68:5+50
    assume {:print "$at(256,2480,2530)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_consensus_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,2480,2530)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,11):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:67:1+135
    assume {:print "$at(256,2397,2532)"} true;
    assume $IsValid'$1_option_Option'$1_string_String''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:68:5+50
    assume {:print "$at(256,2480,2530)"} true;
    assume {:print "$track_return(173,11,0,$1_option_Option'$1_string_String'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:69:1+1
    assume {:print "$at(256,2531,2532)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:69:1+1
    assume {:print "$at(256,2531,2532)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:69:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:69:1+1
    assume {:print "$at(256,2531,2532)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_consensus_pubkey_bytes_spec [baseline] at ./sources/validator_info_specs.move:82:1+149
function $0_validator_info_next_epoch_consensus_pubkey_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'');

procedure {:inline 1} $0_validator_info_next_epoch_consensus_pubkey_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'')
{
    // declare local variables
    var $t1: $1_option_Option'vec'u8'';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'vec'u8''': $1_option_Option'vec'u8'';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:82:1+1
    assume {:print "$at(256,3094,3095)"} true;
    assume {:print "$track_local(173,14,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_consensus_pubkey_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:83:5+55
    assume {:print "$at(256,3186,3241)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_consensus_pubkey_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,3186,3241)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,14):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:82:1+149
    assume {:print "$at(256,3094,3243)"} true;
    assume $IsValid'$1_option_Option'vec'u8'''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:83:5+55
    assume {:print "$at(256,3186,3241)"} true;
    assume {:print "$track_return(173,14,0,$1_option_Option'vec'u8''):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:84:1+1
    assume {:print "$at(256,3242,3243)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:84:1+1
    assume {:print "$at(256,3242,3243)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:84:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:84:1+1
    assume {:print "$at(256,3242,3243)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_mpc_data_bytes_spec [baseline] at ./sources/validator_info_specs.move:87:1+143
function $0_validator_info_next_epoch_mpc_data_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''');

procedure {:inline 1} $0_validator_info_next_epoch_mpc_data_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''')
{
    // declare local variables
    var $t1: $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$2_table_vec_TableVec'vec'u8'''': $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:87:1+1
    assume {:print "$at(256,3326,3327)"} true;
    assume {:print "$track_local(173,15,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_mpc_data_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:88:5+47
    assume {:print "$at(256,3420,3467)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_mpc_data_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,3420,3467)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,15):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:87:1+143
    assume {:print "$at(256,3326,3469)"} true;
    assume $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:88:5+47
    assume {:print "$at(256,3420,3467)"} true;
    assume {:print "$track_return(173,15,0,$1_option_Option'$2_table_vec_TableVec'vec'u8'''):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:89:1+1
    assume {:print "$at(256,3468,3469)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:89:1+1
    assume {:print "$at(256,3468,3469)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:89:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:89:1+1
    assume {:print "$at(256,3468,3469)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_network_address_spec [baseline] at ./sources/validator_info_specs.move:57:1+131
function $0_validator_info_next_epoch_network_address$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String');

procedure {:inline 1} $0_validator_info_next_epoch_network_address(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String')
{
    // declare local variables
    var $t1: $1_option_Option'$1_string_String';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$1_string_String'': $1_option_Option'$1_string_String';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:57:1+1
    assume {:print "$at(256,1977,1978)"} true;
    assume {:print "$track_local(173,9,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_network_address($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:58:5+48
    assume {:print "$at(256,2058,2106)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_network_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,2058,2106)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,9):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:57:1+131
    assume {:print "$at(256,1977,2108)"} true;
    assume $IsValid'$1_option_Option'$1_string_String''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:58:5+48
    assume {:print "$at(256,2058,2106)"} true;
    assume {:print "$track_return(173,9,0,$1_option_Option'$1_string_String'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:59:1+1
    assume {:print "$at(256,2107,2108)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:59:1+1
    assume {:print "$at(256,2107,2108)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:59:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:59:1+1
    assume {:print "$at(256,2107,2108)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_network_pubkey_bytes_spec [baseline] at ./sources/validator_info_specs.move:77:1+145
function $0_validator_info_next_epoch_network_pubkey_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'');

procedure {:inline 1} $0_validator_info_next_epoch_network_pubkey_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'')
{
    // declare local variables
    var $t1: $1_option_Option'vec'u8'';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'vec'u8''': $1_option_Option'vec'u8'';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:77:1+1
    assume {:print "$at(256,2858,2859)"} true;
    assume {:print "$track_local(173,13,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_network_pubkey_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:78:5+53
    assume {:print "$at(256,2948,3001)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_network_pubkey_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,2948,3001)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,13):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:77:1+145
    assume {:print "$at(256,2858,3003)"} true;
    assume $IsValid'$1_option_Option'vec'u8'''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:78:5+53
    assume {:print "$at(256,2948,3001)"} true;
    assume {:print "$track_return(173,13,0,$1_option_Option'vec'u8''):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:79:1+1
    assume {:print "$at(256,3002,3003)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:79:1+1
    assume {:print "$at(256,3002,3003)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:79:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:79:1+1
    assume {:print "$at(256,3002,3003)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_p2p_address_spec [baseline] at ./sources/validator_info_specs.move:62:1+123
function $0_validator_info_next_epoch_p2p_address$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String');

procedure {:inline 1} $0_validator_info_next_epoch_p2p_address(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$1_string_String')
{
    // declare local variables
    var $t1: $1_option_Option'$1_string_String';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$1_string_String'': $1_option_Option'$1_string_String';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:62:1+1
    assume {:print "$at(256,2188,2189)"} true;
    assume {:print "$track_local(173,10,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_p2p_address($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:63:5+44
    assume {:print "$at(256,2265,2309)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_p2p_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,2265,2309)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,10):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:62:1+123
    assume {:print "$at(256,2188,2311)"} true;
    assume $IsValid'$1_option_Option'$1_string_String''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:63:5+44
    assume {:print "$at(256,2265,2309)"} true;
    assume {:print "$track_return(173,10,0,$1_option_Option'$1_string_String'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:64:1+1
    assume {:print "$at(256,2310,2311)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:64:1+1
    assume {:print "$at(256,2310,2311)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:64:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:64:1+1
    assume {:print "$at(256,2310,2311)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::next_epoch_protocol_pubkey_bytes_spec [baseline] at ./sources/validator_info_specs.move:72:1+147
function $0_validator_info_next_epoch_protocol_pubkey_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'');

procedure {:inline 1} $0_validator_info_next_epoch_protocol_pubkey_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'vec'u8'')
{
    // declare local variables
    var $t1: $1_option_Option'vec'u8'';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'vec'u8''': $1_option_Option'vec'u8'';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:72:1+1
    assume {:print "$at(256,2622,2623)"} true;
    assume {:print "$track_local(173,12,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::next_epoch_protocol_pubkey_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:73:5+54
    assume {:print "$at(256,2713,2767)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_next_epoch_protocol_pubkey_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,2713,2767)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,12):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:72:1+147
    assume {:print "$at(256,2622,2769)"} true;
    assume $IsValid'$1_option_Option'vec'u8'''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:73:5+54
    assume {:print "$at(256,2713,2767)"} true;
    assume {:print "$track_return(173,12,0,$1_option_Option'vec'u8''):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:74:1+1
    assume {:print "$at(256,2768,2769)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:74:1+1
    assume {:print "$at(256,2768,2769)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:74:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:74:1+1
    assume {:print "$at(256,2768,2769)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::p2p_address_spec [baseline] at ./sources/validator_info_specs.move:22:1+93
function $0_validator_info_p2p_address$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String);

procedure {:inline 1} $0_validator_info_p2p_address(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_string_String': $1_string_String;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:22:1+1
    assume {:print "$at(256,648,649)"} true;
    assume {:print "$track_local(173,2,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::p2p_address($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:23:5+33
    assume {:print "$at(256,706,739)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_p2p_address$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,706,739)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:22:1+93
    assume {:print "$at(256,648,741)"} true;
    assume $IsValid'$1_string_String'($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:23:5+33
    assume {:print "$at(256,706,739)"} true;
    assume {:print "$track_return(173,2,0,$1_string_String):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:24:1+1
    assume {:print "$at(256,740,741)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:24:1+1
    assume {:print "$at(256,740,741)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:24:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:24:1+1
    assume {:print "$at(256,740,741)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::previous_mpc_data_bytes_spec [baseline] at ./sources/validator_info_specs.move:92:1+139
function $0_validator_info_previous_mpc_data_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''');

procedure {:inline 1} $0_validator_info_previous_mpc_data_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $1_option_Option'$2_table_vec_TableVec'vec'u8''')
{
    // declare local variables
    var $t1: $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$1_option_Option'$2_table_vec_TableVec'vec'u8'''': $1_option_Option'$2_table_vec_TableVec'vec'u8''';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:92:1+1
    assume {:print "$at(256,3550,3551)"} true;
    assume {:print "$track_local(173,16,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::previous_mpc_data_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:93:5+45
    assume {:print "$at(256,3642,3687)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_previous_mpc_data_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,3642,3687)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,16):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:92:1+139
    assume {:print "$at(256,3550,3689)"} true;
    assume $IsValid'$1_option_Option'$2_table_vec_TableVec'vec'u8''''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:93:5+45
    assume {:print "$at(256,3642,3687)"} true;
    assume {:print "$track_return(173,16,0,$1_option_Option'$2_table_vec_TableVec'vec'u8'''):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:94:1+1
    assume {:print "$at(256,3688,3689)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:94:1+1
    assume {:print "$at(256,3688,3689)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:94:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:94:1+1
    assume {:print "$at(256,3688,3689)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::protocol_pubkey_bytes_spec [baseline] at ./sources/validator_info_specs.move:32:1+117
function $0_validator_info_protocol_pubkey_bytes$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int));

procedure {:inline 1} $0_validator_info_protocol_pubkey_bytes(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'vec'u8'': Vec (int);
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:32:1+1
    assume {:print "$at(256,1000,1001)"} true;
    assume {:print "$track_local(173,4,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::protocol_pubkey_bytes($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:33:5+43
    assume {:print "$at(256,1072,1115)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_protocol_pubkey_bytes$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,1072,1115)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:32:1+117
    assume {:print "$at(256,1000,1117)"} true;
    assume $IsValid'vec'u8''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:33:5+43
    assume {:print "$at(256,1072,1115)"} true;
    assume {:print "$track_return(173,4,0,vec'u8'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:34:1+1
    assume {:print "$at(256,1116,1117)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:34:1+1
    assume {:print "$at(256,1116,1117)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:34:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:34:1+1
    assume {:print "$at(256,1116,1117)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun validator_info_specs::protocol_pubkey_spec [baseline] at ./sources/validator_info_specs.move:37:1+118
function $0_validator_info_protocol_pubkey$opaque(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $2_group_ops_Element'$2_bls12381_UncompressedG1');

procedure {:inline 1} $0_validator_info_protocol_pubkey(_$t0: $0_validator_info_ValidatorInfo) returns ($ret0: $2_group_ops_Element'$2_bls12381_UncompressedG1')
{
    // declare local variables
    var $t1: $2_group_ops_Element'$2_bls12381_UncompressedG1';
    var $t2: int;
    var $t0: $0_validator_info_ValidatorInfo;
    var $temp_0'$0_validator_info_ValidatorInfo': $0_validator_info_ValidatorInfo;
    var $temp_0'$2_group_ops_Element'$2_bls12381_UncompressedG1'': $2_group_ops_Element'$2_bls12381_UncompressedG1';
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./sources/validator_info_specs.move:37:1+1
    assume {:print "$at(256,1190,1191)"} true;
    assume {:print "$track_local(173,5,0,$0_validator_info_ValidatorInfo):", $t0} $t0 == $t0;

    // $t1 := validator_info::protocol_pubkey($t0) on_abort goto L2 with $t2 at ./sources/validator_info_specs.move:38:5+37
    assume {:print "$at(256,1269,1306)"} true;
    havoc $abort_flag;
    $t1 := $0_validator_info_protocol_pubkey$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(256,1269,1306)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(173,5):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/validator_info_specs.move:37:1+118
    assume {:print "$at(256,1190,1308)"} true;
    assume $IsValid'$2_group_ops_Element'$2_bls12381_UncompressedG1''($t1);

    // trace_return[0]($t1) at ./sources/validator_info_specs.move:38:5+37
    assume {:print "$at(256,1269,1306)"} true;
    assume {:print "$track_return(173,5,0,$2_group_ops_Element'$2_bls12381_UncompressedG1'):", $t1} $t1 == $t1;

    // label L1 at ./sources/validator_info_specs.move:39:1+1
    assume {:print "$at(256,1307,1308)"} true;
L1:

    // return $t1 at ./sources/validator_info_specs.move:39:1+1
    assume {:print "$at(256,1307,1308)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/validator_info_specs.move:39:1+1
L2:

    // abort($t2) at ./sources/validator_info_specs.move:39:1+1
    assume {:print "$at(256,1307,1308)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
