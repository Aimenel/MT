// 
// Translation of SIL program.
// 
// Date:         2016-04-27 15:35:14
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
axiom ((forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
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
)) && (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), P#everUsed(pm_f), IsPredicateField(pm_f) }
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
// Translation of all fields
// ==================================================

const unique f_5: Field NormalField int;
axiom !IsPredicateField(f_5);
axiom !IsWandField(f_5);

// ==================================================
// Translation of predicate P
// ==================================================

type PredicateType_P;
function P(x_1: Ref, y_1: int): Field PredicateType_P int;
function P#sm(x_1: Ref, y_1: int): Field PredicateType_P PMaskType;
axiom (forall x_1: Ref, y_1: int ::
  { PredicateMaskField(P(x_1, y_1)) }
  PredicateMaskField(P(x_1, y_1)) == P#sm(x_1, y_1)
);
axiom (forall x_1: Ref, y_1: int ::
  { P(x_1, y_1) }
  IsPredicateField(P(x_1, y_1))
);
function P#trigger<A>(Heap: HeapType, pred: (Field A int)): bool;
function P#everUsed<A>(pred: (Field A int)): bool;
axiom (forall x_1: Ref, y_1: int, x2: Ref, y2: int ::
  { P(x_1, y_1), P(x2, y2) }
  P(x_1, y_1) == P(x2, y2) ==> x_1 == x2 && y_1 == y2
);
axiom (forall x_1: Ref, y_1: int, x2: Ref, y2: int ::
  { P#sm(x_1, y_1), P#sm(x2, y2) }
  P#sm(x_1, y_1) == P#sm(x2, y2) ==> x_1 == x2 && y_1 == y2
);

axiom (forall Heap: HeapType, x_1: Ref, y_1: int ::
  { P#trigger(Heap, P(x_1, y_1)) }
  P#everUsed(P(x_1, y_1))
);

// ==================================================
// Translation of method m
// ==================================================

procedure m(a_2: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var oldVersion: int;
  var newVersion: int;
  var v1: int;
  var freshVersion: int;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume a_2 == null || Heap[a_2, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    Mask[null, P(a_2, 0)] := Mask[null, P(a_2, 0)] + perm;
    
    // -- Extra unfolding of predicate
      
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  PostHeap := Heap;
  PostMask := Mask;
  havoc PostHeap;
  PostMask := ZeroMask;
  assume state(PostHeap, PostMask);
  if (*) {
    // Checked inhaling of postcondition to check definedness
    perm := FullPerm;
    PostMask[null, P(a_2, 0)] := PostMask[null, P(a_2, 0)] + perm;
    
    // -- Extra unfolding of predicate
      
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: unfold acc(P(a, 0), write) -- in.sil@12.5
    assume P#trigger(Heap, P(a_2, 0));
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Unfolding P(a, 0) might fail. There might be insufficient permission to access P(a, 0). (in.sil@12.5) [24]"}
        perm <= Mask[null, P(a_2, 0)];
    }
    Mask[null, P(a_2, 0)] := Mask[null, P(a_2, 0)] - perm;
    
    // -- Update version of predicate
      if (HasDirectPerm(Mask, null, P(a_2, 0))) {
        oldVersion := Heap[null, P(a_2, 0)];
        havoc newVersion;
        assume oldVersion < newVersion;
        Heap[null, P(a_2, 0)] := newVersion;
      }
    perm := FullPerm;
    assume a_2 != null;
    Mask[a_2, f_5] := Mask[a_2, f_5] + perm;
    assume state(Heap, Mask);
    assume state(Heap, Mask);
  
  // -- Translating statement: v1 := a.f -- in.sil@13.5
    
    // -- Check definedness of a.f
      assert {:msg "  Assignment might fail. There might be insufficient permission to access a.f. (in.sil@13.5) [25]"}
        HasDirectPerm(Mask, a_2, f_5);
      assume state(Heap, Mask);
    v1 := Heap[a_2, f_5];
    assume state(Heap, Mask);
  
  // -- Translating statement: a.f := 2 -- in.sil@14.2
    
    // -- Check definedness of a.f
      assert {:msg "  Assignment might fail. Receiver of a.f might be null. (in.sil@14.2) [26]"}
        a_2 != null;
      assert {:msg "  Assignment might fail. There might be insufficient permission to access a.f. (in.sil@14.2) [27]"}
        HasDirectPerm(Mask, a_2, f_5);
      assume state(Heap, Mask);
    Heap[a_2, f_5] := 2;
    assert {:msg "  Assignment might fail. There might be insufficient permission to access a.f. (in.sil@14.2) [28]"}
      FullPerm == Mask[a_2, f_5];
    assume state(Heap, Mask);
  
  // -- Translating statement: fold acc(P(a, 0), write) -- in.sil@16.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Folding P(a, 0) might fail. Receiver of a.f might be null. (in.sil@16.5) [30]"}
      a_2 != null;
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Folding P(a, 0) might fail. There might be insufficient permission to access a.f. (in.sil@16.5) [31]"}
        perm <= Mask[a_2, f_5];
    }
    Mask[a_2, f_5] := Mask[a_2, f_5] - perm;
    // Phase 2: abstract read permissions (and scaled abstract read permissions)
    // Phase 3: all remaining permissions (containing read permissions, but in a negative context)
    perm := FullPerm;
    Mask[null, P(a_2, 0)] := Mask[null, P(a_2, 0)] + perm;
    
    // -- Extra unfolding of predicate
      
    assume state(Heap, Mask);
    Heap[null, P#sm(a_2, 0)] := ZeroPMask;
    havoc freshVersion;
    Heap[null, P(a_2, 0)] := freshVersion;
    Heap[null, P#sm(a_2, 0)][a_2, f_5] := true;
    assume P#trigger(Heap, P(a_2, 0));
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    havoc ExhaleHeap;
    // Phase 1: pure assertions and fixed permissions
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of m might not hold. There might be insufficient permission to access P(a, 0). (in.sil@10.10) [32]"}
        perm <= Mask[null, P(a_2, 0)];
    }
    Mask[null, P(a_2, 0)] := Mask[null, P(a_2, 0)] - perm;
    // Finish exhale
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}