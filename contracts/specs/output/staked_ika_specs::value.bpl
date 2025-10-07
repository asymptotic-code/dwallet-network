
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


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
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


// ==================================================================================
// Native VecSet

// ==================================================================================
// Native TableVec

// ==================================================================================
// Native VecMap

// ==================================================================================
// Native Table

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

// fun staked_ika_specs::value [verification] at ./sources/staked_ika_specs.move:11:1+67
procedure {:timeLimit 3000} $0_staked_ika_value$verify(_$t0: $0_staked_ika_StakedIka) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/staked_ika_specs.move:11:1+1
    assume {:print "$at(255,284,285)"} true;
    assume $IsValid'$0_staked_ika_StakedIka'($t0);

    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:11:1+1
    assume {:print "$track_local(167,1,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::value($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,328,349)"} true;
    call $t1 := $0_staked_ika_value$impl($t0);
    if ($abort_flag) {
        assume {:print "$at(255,328,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$track_return(167,1,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:13:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::value [baseline] at ./sources/staked_ika_specs.move:11:1+67
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
    assume {:print "$at(255,284,285)"} true;
    assume {:print "$track_local(167,1,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::value($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,328,349)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_value$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,328,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:11:1+67
    assume {:print "$at(255,284,351)"} true;
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,328,349)"} true;
    assume {:print "$track_return(167,1,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:13:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::value [baseline] at ./sources/staked_ika_specs.move:11:1+67
procedure {:inline 1} $0_staked_ika_value$asserts(_$t0: $0_staked_ika_StakedIka) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // label L1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
L1:

    // label L2 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::value [verification] at ./sources/staked_ika_specs.move:11:1+67
procedure {:timeLimit 3000} $0_staked_ika_value$spec_no_abort_check$verify(_$t0: $0_staked_ika_StakedIka) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $0_staked_ika_StakedIka;
    var $temp_0'$0_staked_ika_StakedIka': $0_staked_ika_StakedIka;
    var $temp_0'u64': int;
    var $abort_if_cond: bool;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/staked_ika_specs.move:11:1+1
    assume {:print "$at(255,284,285)"} true;
    assume $IsValid'$0_staked_ika_StakedIka'($t0);

    // trace_local[sw]($t0) at ./sources/staked_ika_specs.move:11:1+1
    assume {:print "$track_local(167,1,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::value($t0) at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,328,349)"} true;
    $t1 := $0_staked_ika_value$opaque($t0);

    // $t1 := havoc[val]() at ./sources/staked_ika_specs.move:11:1+67
    assume {:print "$at(255,284,351)"} true;
    havoc $t1;

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:11:1+67
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:12:5+21
    assume {:print "$at(255,328,349)"} true;
    assume {:print "$track_return(167,1,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
L1:

    // label L2 at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:13:1+1
    assume {:print "$at(255,350,351)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::validator_id [baseline] at ./sources/staked_ika_specs.move:6:1+80
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
    assume {:print "$at(255,195,223)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_validator_id$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,195,223)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:6:1+80
    assume {:print "$at(255,145,225)"} true;
    assume $IsValid'$2_object_ID'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:7:5+28
    assume {:print "$at(255,195,223)"} true;
    assume {:print "$track_return(167,0,0,$2_object_ID):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:8:1+1
    assume {:print "$at(255,224,225)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:8:1+1
    assume {:print "$at(255,224,225)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:8:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:8:1+1
    assume {:print "$at(255,224,225)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::activation_epoch [baseline] at ./sources/staked_ika_specs.move:16:1+89
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
    assume {:print "$at(255,421,422)"} true;
    assume {:print "$track_local(167,2,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::activation_epoch($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:17:5+32
    assume {:print "$at(255,476,508)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_activation_epoch$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,476,508)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:16:1+89
    assume {:print "$at(255,421,510)"} true;
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:17:5+32
    assume {:print "$at(255,476,508)"} true;
    assume {:print "$track_return(167,2,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:18:1+1
    assume {:print "$at(255,509,510)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:18:1+1
    assume {:print "$at(255,509,510)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:18:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:18:1+1
    assume {:print "$at(255,509,510)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::is_staked [baseline] at ./sources/staked_ika_specs.move:21:1+76
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
    assume {:print "$at(255,573,574)"} true;
    assume {:print "$track_local(167,3,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::is_staked($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:22:5+25
    assume {:print "$at(255,622,647)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_is_staked$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,622,647)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,3):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:21:1+76
    assume {:print "$at(255,573,649)"} true;
    assume $IsValid'bool'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:22:5+25
    assume {:print "$at(255,622,647)"} true;
    assume {:print "$track_return(167,3,0,bool):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:23:1+1
    assume {:print "$at(255,648,649)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:23:1+1
    assume {:print "$at(255,648,649)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:23:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:23:1+1
    assume {:print "$at(255,648,649)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::is_withdrawing [baseline] at ./sources/staked_ika_specs.move:26:1+86
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
    assume {:print "$at(255,717,718)"} true;
    assume {:print "$track_local(167,4,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::is_withdrawing($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:27:5+30
    assume {:print "$at(255,771,801)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_is_withdrawing$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,771,801)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:26:1+86
    assume {:print "$at(255,717,803)"} true;
    assume $IsValid'bool'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:27:5+30
    assume {:print "$at(255,771,801)"} true;
    assume {:print "$track_return(167,4,0,bool):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:28:1+1
    assume {:print "$at(255,802,803)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:28:1+1
    assume {:print "$at(255,802,803)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:28:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:28:1+1
    assume {:print "$at(255,802,803)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::withdraw_epoch [baseline] at ./sources/staked_ika_specs.move:31:1+85
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
    assume {:print "$at(255,955,956)"} true;
L1:

    // label L2 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,955,956)"} true;
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,955,956)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staked_ika_specs::withdraw_epoch [baseline] at ./sources/staked_ika_specs.move:31:1+85
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
    assume {:print "$at(255,871,872)"} true;
    assume {:print "$track_local(167,5,0,$0_staked_ika_StakedIka):", $t0} $t0 == $t0;

    // $t1 := staked_ika::withdraw_epoch($t0) on_abort goto L2 with $t2 at ./sources/staked_ika_specs.move:32:5+30
    assume {:print "$at(255,924,954)"} true;
    havoc $abort_flag;
    $t1 := $0_staked_ika_withdraw_epoch$opaque($t0);
    if ($abort_flag) {
        assume {:print "$at(255,924,954)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(167,5):", $t2} $t2 == $t2;
        goto L2;
    }

    // assume WellFormed($t1) at ./sources/staked_ika_specs.move:31:1+85
    assume {:print "$at(255,871,956)"} true;
    assume $IsValid'u64'($t1);

    // trace_return[0]($t1) at ./sources/staked_ika_specs.move:32:5+30
    assume {:print "$at(255,924,954)"} true;
    assume {:print "$track_return(167,5,0,u64):", $t1} $t1 == $t1;

    // label L1 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,955,956)"} true;
L1:

    // return $t1 at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,955,956)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/staked_ika_specs.move:33:1+1
L2:

    // abort($t2) at ./sources/staked_ika_specs.move:33:1+1
    assume {:print "$at(255,955,956)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
