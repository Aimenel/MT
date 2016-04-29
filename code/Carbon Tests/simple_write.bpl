// 
// Translation of SIL program.
// 
// Date:         2016-04-25 10:39:22
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

const unique x_1: Field NormalField int;
axiom !IsPredicateField(x_1);
axiom !IsWandField(x_1);

// ==================================================
// Translation of method foo
// ==================================================

procedure foo(this: Ref) returns ()
  modifies Heap, Mask;
{
  var perm: Perm;
  var PostHeap: HeapType;
  var PostMask: MaskType;
  var ExhaleHeap: HeapType;
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Assumptions about method arguments
    assume this == null || Heap[this, $allocated];
  
  // -- Checked inhaling of precondition
    perm := FullPerm;
    assume this != null;
    Mask[this, x_1] := Mask[this, x_1] + perm;
    assume state(Heap, Mask);
    
    // -- Check definedness of this.x == 4
      assert {:msg "  Contract might not be well-formed. Receiver of this.x might be null. (in.sil@6.10) [31]"}
        this != null;
      assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.x. (in.sil@6.10) [32]"}
        HasDirectPerm(Mask, this, x_1);
      assume state(Heap, Mask);
    assume Heap[this, x_1] == 4;
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
    assume this != null;
    PostMask[this, x_1] := PostMask[this, x_1] + perm;
    assume state(PostHeap, PostMask);
    
    // -- Check definedness of this.x == 3
      assert {:msg "  Contract might not be well-formed. Receiver of this.x might be null. (in.sil@8.9) [33]"}
        this != null;
      assert {:msg "  Contract might not be well-formed. There might be insufficient permission to access this.x. (in.sil@8.9) [34]"}
        HasDirectPerm(PostMask, this, x_1);
      assume state(PostHeap, PostMask);
    assume PostHeap[this, x_1] == 3;
    assume state(PostHeap, PostMask);
    // Stop execution
    assume false;
  }
  
  // -- Translating statement: this.x := 3 -- in.sil@10.5
    
    // -- Check definedness of this.x
      assert {:msg "  Assignment might fail. Receiver of this.x might be null. (in.sil@10.5) [35]"}
        this != null;
      assert {:msg "  Assignment might fail. There might be insufficient permission to access this.x. (in.sil@10.5) [36]"}
        HasDirectPerm(Mask, this, x_1);
      assume state(Heap, Mask);
    Heap[this, x_1] := 3;
    assert {:msg "  Assignment might fail. There might be insufficient permission to access this.x. (in.sil@10.5) [37]"}
      FullPerm == Mask[this, x_1];
    assume state(Heap, Mask);
  
  // -- Exhaling postcondition
    havoc ExhaleHeap;
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Postcondition of foo might not hold. Receiver of this.x might be null. (in.sil@7.9) [38]"}
      this != null;
    perm := NoPerm;
    perm := perm + FullPerm;
    if (perm != NoPerm) {
      assert {:msg "  Postcondition of foo might not hold. There might be insufficient permission to access this.x. (in.sil@7.9) [39]"}
        perm <= Mask[this, x_1];
    }
    Mask[this, x_1] := Mask[this, x_1] - perm;
    assert {:msg "  Postcondition of foo might not hold. Assertion this.x == 3 might not hold. (in.sil@8.9) [40]"}
      Heap[this, x_1] == 3;
    // Finish exhale
    assume IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask);
    Heap := ExhaleHeap;
}