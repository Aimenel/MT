// 
// Translation of SIL program.
// 
// Date:         2016-04-25 10:56:04
// Tool:         carbon 1.0
// Arguments: :  --print out.bpl in.sil
// Dependencies:
//   Boogie , located at C:\Users\nadja\Documents\boogie\Binaries\Boogie.exe.
//   Z3 4.4.0, located at C:\Users\nadja\Documents\z3-4.4.0-x64-win\bin\z3.exe.
// 

// ==================================================
// Preamble of State module.
// ==================================================

function state(Heap: HeapType, Mask: MaskType): bool;

// ==================================================
// Preamble of Heap module.
// ==================================================

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType = <A, B> [Ref, Field A B]B;
const unique $allocated: Field NormalField bool;
axiom (forall o: Ref, f: (Field NormalField Ref), Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask), Heap[o, f] }
  Heap[o, f] == null || Heap[Heap[o, f], $allocated]
);
function IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function IsPredicateField<A, B>(f_1: (Field A B)): bool;
function IsWandField<A, B>(f_1: (Field A B)): bool;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
) && (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[null, PredicateMaskField(pm_f)], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { Heap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  ) && (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
) && (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[null, PredicateMaskField(pm_f)], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { Heap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  ) && (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
) && (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);

// ==================================================
// Preamble of Permission module (with quantified permission support).
// ==================================================

type Perm = real;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == 0.000000000
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function PredicateMaskField<A>(f_4: (Field A int)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function Perm(a: real, b: real): Perm;
function GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  GoodMask(Mask) ==> Mask[o_1, f_3] >= 0.000000000 && ((GoodMask(Mask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> Mask[o_1, f_3] <= 1.000000000)
);
function HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> Mask[o_1, f_3] > 0.000000000
);
function sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom ((forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
) && (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
)) && (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
);
// ==================================================
// Functions used as inverse of receiver expressions in quantified permissions during inhale and exhale
// ==================================================

function invRecv1(recv: Ref): int;
function invRecv2(recv: Ref): int;

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function FrameFragment<T>(t: T): FrameType;
function CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// Function for recording enclosure of one predicate instance in another
function InsidePredicate<A, B>(x: Ref, p: (Field A int), v: int, y: Ref, q: (Field B int), w: int): bool;
const unique special_ref: Ref;
// Transitivity of InsidePredicate
axiom (forall <A, B, C> x: Ref, p: (Field A int), v: int, y: Ref, q: (Field B int), w: int, z: Ref, r: (Field C int), u: int ::
  { InsidePredicate(x, p, v, y, q, w), InsidePredicate(y, q, w, z, r, u) }
  InsidePredicate(x, p, v, y, q, w) && InsidePredicate(y, q, w, z, r, u) ==> InsidePredicate(x, p, v, z, r, u)
);
// Knowledge that two identical instances of the same predicate cannot be inside each other
axiom (forall <A> x: Ref, p: (Field A int), v: int, y: Ref, w: int ::
  { InsidePredicate(x, p, v, y, p, w) }
  InsidePredicate(x, p, v, y, p, w) ==> x != y
);

// ==================================================
// Translation of domain IArray
// ==================================================

// The type for domain IArray
type IArrayDomainType;

// Translation of domain function loc
function loc(a_2: IArrayDomainType, i: int): Ref;

// Translation of domain function len
function len(a_2: IArrayDomainType): int;

// Translation of domain function first
function first(r_1: Ref): IArrayDomainType;

// Translation of domain function second
function second(r_1: Ref): int;

// Translation of domain axiom all_diff
axiom (forall a_3: IArrayDomainType, i_1: int ::
  { loc(a_3, i_1) }
  first(loc(a_3, i_1)) == a_3 && second(loc(a_3, i_1)) == i_1
);

// Translation of domain axiom length_nonneg
axiom (forall a_3: IArrayDomainType ::
  { len(a_3) }
  len(a_3) >= 0
);

// ==================================================
// Translation of all fields
// ==================================================

const unique val: Field NormalField int;
axiom !IsPredicateField(val);
axiom !IsWandField(val);

// ==================================================
// Translation of method max
// ==================================================

procedure max(a_3: IArrayDomainType) returns (at: int)
  modifies Heap, Mask;
{
  var QPMask: MaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: inhale (forall j: Int :: (0 <= j) && (j <= len(a)) ==> acc(loc(a, j).val, write)) -- in.sil@3.5
    havoc QPMask;
    //define inverse
	assume (forall j_1: int ::
      { loc(a_3, j_1) }
      0 <= j_1 && j_1 <= len(a_3) ==> invRecv1(loc(a_3, j_1)) == j_1
    );
    assume (forall o_2: Ref ::
      { invRecv1(o_2) }
      0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3) ==> loc(a_3, invRecv1(o_2)) == o_2
    );
	/check non-null
    assume (forall j_1: int ::
      
      0 <= j_1 && j_1 <= len(a_3) ==> loc(a_3, j_1) != null
    );
	//injective access
    assume (forall j_1: int, v2: int ::
      
      (j_1 != v2 && (0 <= j_1 && j_1 <= len(a_3))) && (0 <= v2 && v2 <= len(a_3)) ==> loc(a_3, j_1) != loc(a_3, v2)
    );
    assume ((forall o_2: Ref ::
      { Mask[o_2, val] }
      (0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3) ==> QPMask[o_2, val] == Mask[o_2, val] + FullPerm) && (!(0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3)) ==> QPMask[o_2, val] == Mask[o_2, val])
    ) && (forall o_2: Ref ::
      { QPMask[o_2, val] }
      (0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3) ==> QPMask[o_2, val] == Mask[o_2, val] + FullPerm) && (!(0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3)) ==> QPMask[o_2, val] == Mask[o_2, val])
    )) && (forall o_2: Ref ::
      { invRecv1(o_2) }
      (0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3) ==> QPMask[o_2, val] == Mask[o_2, val] + FullPerm) && (!(0 <= invRecv1(o_2) && invRecv1(o_2) <= len(a_3)) ==> QPMask[o_2, val] == Mask[o_2, val])
    );
    assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
      { Mask[o_2, f_4] }
      f_4 != val ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
    ) && (forall <A, B> o_2: Ref, f_4: (Field A B) ::
      { QPMask[o_2, f_4] }
      f_4 != val ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
    );
    Mask := QPMask;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: exhale (forall j: Int :: (0 <= j) && (j <= len(a)) ==> acc(loc(a, j).val, write)) -- in.sil@4.5
    havoc ExhaleHeap;
    // Phase 1: pure assertions and fixed permissions
    havoc QPMask;
    assert {:msg "  Exhale might fail. Receiver of loc(a, j).val might be null. (in.sil@4.5) [4]"}
      (forall j_3: int ::
      
      0 <= j_3 && j_3 <= len(a_3) ==> loc(a_3, j_3) != null
    );
    assert {:msg "  Exhale might fail. There might be insufficient permission to access loc(a, j).val. (in.sil@4.5) [6]"}
      (forall j_3: int ::
      
      0 <= j_3 && j_3 <= len(a_3) ==> Mask[loc(a_3, j_3), val] >= FullPerm
    );
    
    // -- check if receiver loc(a, j) is injective
      assert {:msg "  Exhale might fail. Receiver of loc(a, j).val might not be injective. (in.sil@4.5) [7]"}
        (forall j_3: int, v2: int ::
        
        (j_3 != v2 && (0 <= j_3 && j_3 <= len(a_3))) && (0 <= v2 && v2 <= len(a_3)) ==> loc(a_3, j_3) != loc(a_3, v2)
      );
    
    // -- assumptions for inverse of receiver loc(a, j)
      assume (forall j_3: int ::
        { loc(a_3, j_3) }
        0 <= j_3 && j_3 <= len(a_3) ==> invRecv2(loc(a_3, j_3)) == j_3
      );
      assume (forall o_2: Ref ::
        { invRecv2(o_2) }
        0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3) ==> loc(a_3, invRecv2(o_2)) == o_2
      );
	  //{}:: Triger if you see the term {}: instantiate quantifier
    assume ((forall o_2: Ref ::
      { Mask[o_2, val] }
      (0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3) ==> QPMask[o_2, val] == Mask[o_2, val] - FullPerm) && (!(0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3)) ==> QPMask[o_2, val] == Mask[o_2, val])
    ) && (forall o_2: Ref ::
      { QPMask[o_2, val] }
      (0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3) ==> QPMask[o_2, val] == Mask[o_2, val] - FullPerm) && (!(0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3)) ==> QPMask[o_2, val] == Mask[o_2, val])
    )) && (forall o_2: Ref ::
      { invRecv2(o_2) }
      (0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3) ==> QPMask[o_2, val] == Mask[o_2, val] - FullPerm) && (!(0 <= invRecv2(o_2) && invRecv2(o_2) <= len(a_3)) ==> QPMask[o_2, val] == Mask[o_2, val])
    );
    assume (forall <A, B> o_2: Ref, f_4: (Field A B) ::
      { Mask[o_2, f_4] }
      f_4 != val ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
    ) && (forall <A, B> o_2: Ref, f_4: (Field A B) ::
      { QPMask[o_2, f_4] }
      f_4 != val ==> Mask[o_2, f_4] == QPMask[o_2, f_4]
    );
    Mask := QPMask;
    // Finish exhale
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
    assume state(Heap, Mask);
}