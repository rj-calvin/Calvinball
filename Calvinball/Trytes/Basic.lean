import Duality.LinearProgramming

abbrev Tryte := Extend (Fin 6)
def Tryte.mk : Nat → Tryte := toE ∘ Fin.ofNat' 6

instance : OfNat Tryte (n : Nat) := ⟨Tryte.mk n⟩

instance : Bot Tryte where bot := none
instance : Top Tryte where top := some none
instance : Inhabited Tryte where default := ⊥

instance : ToString Tryte where
  toString
  | ⊤ => "⊤"
  | ⊥ => "⊥"
  | some (some x) => toString x

namespace Tryte

-- 3-bits make a Tryte.
@[coe] def ofFin8 : Fin 8 → Tryte
| 0 => ⊥
| 7 => ⊤
| x => toE (x - 1)

@[coe] def toFin8 : Tryte → Fin 8
| ⊥ => 0
| ⊤ => 7
| (x : Fin 6) => x + 1

instance : Coe (Fin 8) Tryte := ⟨ofFin8⟩
instance : Coe Tryte (Fin 8) := ⟨toFin8⟩

def add : Tryte → Tryte → Tryte
| ⊥, _ => ⊥
| _, ⊥ => ⊥
| ⊤, _ => ⊤
| _, ⊤ => ⊤
| (x : Fin 6), (y : Fin 6) => x.add y

def neg : Tryte → Tryte
| ⊥ => ⊤
| ⊤ => ⊥
| (x : Fin 6) => toE x.rev

instance : HAdd Tryte Tryte Tryte := ⟨add⟩
instance : Neg Tryte := ⟨neg⟩

end Tryte

namespace Tryte.Orientation

def above : Tryte := ⊤
def up : Tryte := mk 0
def upright : Tryte := mk 1
def downright : Tryte := mk 2
def down : Tryte := mk 3
def downleft : Tryte := mk 4
def upleft : Tryte := mk 5
def below : Tryte := ⊥

end Tryte.Orientation

namespace Tryte.QwertyRightHandKeys

def p : Tryte := ⊤
def kk : Tryte := mk 0
def kl : Tryte := mk 1
def jl : Tryte := mk 2
def jj : Tryte := mk 3
def jh : Tryte := mk 4
def kh : Tryte := mk 5
def n : Tryte := ⊥

end Tryte.QwertyRightHandKeys

namespace Tryte.QwertyLeftHandKeys

def q : Tryte := ⊤
def dd : Tryte := mk 0
def df : Tryte := mk 1
def sf : Tryte := mk 2
def ss : Tryte := mk 3
def sa : Tryte := mk 4
def da : Tryte := mk 5
def v : Tryte := ⊥

end Tryte.QwertyLeftHandKeys

-- indexed by 1-tryte
structure TryteWord where
  mk ::
  bits : Tryte
  word : Vector UInt8 3
deriving Inhabited

-- ⊤ is used here to distinguish coercion from default
@[coe] def TryteWord.ofVec (w : Vector Nat 3) : TryteWord := ⟨⊤, w.map UInt8.ofNat⟩

@[coe] def TryteWord.toVec (W : TryteWord) : Vector Tryte 8 :=
  Vector.map (Tryte.mk ∘ UInt8.toNat)
  $ match W.bits with
  | ⊤ => #v[
    W.word[0].shiftRight 5,
    W.word[0].shiftRight 2,
    W.word[0].shiftLeft 1 |>.land 3 |>.add (W.word[1].shiftRight 7),
    W.word[1].shiftRight 4,
    W.word[1].shiftRight 1,
    W.word[1].shiftLeft 2 |>.land 7 |>.add (W.word[2].shiftRight 6),
    W.word[2].shiftRight 3,
    W.word[2]
  ]
  | ⊥ => #v[
    W.word[2],
    W.word[2].shiftRight 3,
    W.word[1].shiftLeft 2 |>.land 7 |>.add (W.word[2].shiftRight 6),
    W.word[1].shiftRight 1,
    W.word[1].shiftRight 4,
    W.word[0].shiftLeft 1 |>.land 3 |>.add (W.word[1].shiftRight 7),
    W.word[0].shiftRight 2,
    W.word[0].shiftRight 5
  ]
  | 0 => #v[0, 0, 0, 0, 0, 0, 0, W.word[0].shiftRight 2]
  | 1 => #v[0, 0, 0, 0, 0, 0, 0, W.word[0].shiftLeft 1 |>.land 3 |>.add (W.word[1].shiftRight 7)]
  | 2 => #v[0, 0, 0, 0, 0, 0, 0, W.word[1].shiftRight 4]
  | 3 => #v[0, 0, 0, 0, 0, 0, 0, W.word[1].shiftRight 1]
  | 4 => #v[0, 0, 0, 0, 0, 0, 0, W.word[1].shiftLeft 2 |>.land 7 |>.add (W.word[2].shiftRight 6)]
  | 5 => #v[0, 0, 0, 0, 0, 0, 0, W.word[2].shiftRight 3]

def TryteWord.Boundary (W : TryteWord) : Tryte × Tryte :=
  let w := W.toVec
  (w[0], w[7])

instance : Coe (Vector Nat 3) TryteWord := ⟨TryteWord.ofVec⟩
instance : Coe TryteWord (Vector Tryte 8) := ⟨TryteWord.toVec⟩

@[simp] def TryteWord.neg (L : TryteWord) : TryteWord := { L with bits := -L.bits }
instance : Neg TryteWord := ⟨TryteWord.neg⟩

#eval (#v[1, 1, 1] : TryteWord)       |>.toVec.toArray |> toString
#eval (#v[2, 2, 2] : TryteWord)       |>.toVec.toArray |> toString
#eval (#v[3, 3, 3] : TryteWord)       |>.toVec.toArray |> toString
#eval (#v[8, 8, 8] : TryteWord)       |>.toVec.toArray |> toString
#eval (#v[24, 24, 24] : TryteWord)    |>.toVec.toArray |> toString
#eval (#v[192, 192, 192] : TryteWord) |>.toVec.toArray |> toString

def TryteWord.IsRelative (W : TryteWord) : Prop  := W.Boundary.1 = W.Boundary.2
def TryteWord.IsAlien (W : TryteWord) : Prop     := W.Boundary.1 ≠ 0 ∧ ¬W.IsRelative

def TryteWord.IsImpartial (W : TryteWord) : Prop := W.Boundary.1 = 0 ∧ W.Boundary.2 = 1
def TryteWord.IsPartisan (W : TryteWord) : Prop  := W.Boundary.1 = 0 ∧ W.Boundary.2 = 2
def TryteWord.IsValid (W : TryteWord) : Prop     := W.IsImpartial ∨ W.IsPartisan

def TryteWord.IsAbstract (W : TryteWord) : Prop  := ¬W.IsAlien ∧ ¬W.IsValid

def TryteWord.align (W : TryteWord) : (W.IsValid → Part TryteWord) → Part TryteWord :=
  Part.assert W.IsValid

-- indexed by 2-trytes
structure TryteLine where
  bits : Tryte × Tryte
  line : Vector TryteWord 64
deriving Inhabited

def TryteLine.IsSound (L : TryteLine) : Prop := ∃ (i : Fin 64), L.line[i].IsValid
def TryteLine.IsComplete (L : TryteLine) : Prop := ∀ (i : Fin 64), L.line[i].IsValid

def TryteLine.solve (L : TryteLine) : (L.IsComplete → Part TryteLine) → Part TryteLine :=
  Part.assert L.IsComplete

-- indexed by 4-trytes
structure TryteBall where
  bits : Tryte × Tryte × Tryte × Tryte
  ball : Vector TryteLine 4096
deriving Inhabited

def TryteBall.IsSound (B : TryteBall) : Prop := ∃ (i : Fin 4096), B.ball[i].IsSound

def TryteBall.compose (B : TryteBall) : (B.IsSound → Part TryteBall) → Part TryteBall :=
  Part.assert B.IsSound
