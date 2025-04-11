import Duality.LinearProgramming

abbrev Tryte := Extend (Fin 6)
def Tryte.mk : Nat → Tryte := toE ∘ Fin.ofNat' 6

instance : OfNat Tryte (n : Nat) := ⟨Tryte.mk n⟩

instance : Bot Tryte where bot := none
instance : Top Tryte where top := some none
instance : Inhabited Tryte where default := ⊥
instance : DecidableEq Tryte := WithBot.decidableEq

instance : ToString Tryte where
  toString
  | ⊤ => "⊤"
  | ⊥ => "⊥"
  | (x : Fin 6) => toString x

namespace Tryte

-- 3-bits make a Tryte.
@[coe, inline] def ofFin8 : Fin 8 → Tryte
| 0 => ⊥
| 7 => ⊤
| x => toE (x - 1)

@[coe, inline] def toFin8 : Tryte → Fin 8
| ⊤ => 7
| ⊥ => 0
| (x : Fin 6) => x + 1

instance : Coe (Fin 8) Tryte := ⟨ofFin8⟩
instance : Coe Tryte (Fin 8) := ⟨toFin8⟩

instance : HAdd Tryte Tryte Tryte where
  hAdd
  | ⊥, _ => ⊥
  | _, ⊥ => ⊥
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | (x : Fin 6), (y : Fin 6) => x.add y

instance : HSMul Nat Tryte Tryte where
  hSMul
  | _, ⊥ => ⊥
  | 0, _ => 0
  | _, ⊤ => ⊤
  | c, (x : Fin 6) => toE (c * x)

def neg : Tryte → Tryte
| ⊥ => ⊤
| ⊤ => ⊥
| (x : Fin 6) => x.rev

instance : Neg Tryte := ⟨neg⟩

namespace Orientation

def above : Tryte     := ⊤
def up : Tryte        := mk 0
def upright : Tryte   := mk 1
def downright : Tryte := mk 2
def down : Tryte      := mk 3
def downleft : Tryte  := mk 4
def upleft : Tryte    := mk 5
def below : Tryte     := ⊥

end Orientation

namespace QwertyRightHandKeys

def p : Tryte  := ⊤
def kk : Tryte := mk 0
def kl : Tryte := mk 1
def jl : Tryte := mk 2
def jj : Tryte := mk 3
def jh : Tryte := mk 4
def kh : Tryte := mk 5
def n : Tryte  := ⊥

end QwertyRightHandKeys

namespace QwertyLeftHandKeys

def q : Tryte  := ⊤
def dd : Tryte := mk 0
def df : Tryte := mk 1
def sf : Tryte := mk 2
def ss : Tryte := mk 3
def sa : Tryte := mk 4
def da : Tryte := mk 5
def v : Tryte  := ⊥

end QwertyLeftHandKeys

end Tryte

-- indexed by 1-tryte
structure TryteWord where
  mk ::
  bits : Tryte
  word : Vector UInt8 3
deriving Inhabited

namespace TryteWord

-- ⊤ is used here to distinguish coercion from default
@[coe] def ofVec (v : Vector Nat 3) : TryteWord := ⟨⊤, v.map .ofNat⟩

@[coe] def toVec (W : TryteWord) : Vector Tryte 8 :=
  .map go $ match W.bits with
  | ⊤ => #v[w₀₀, w₀₁, w₀₂, w₁₀, w₁₁, w₁₂, w₂₀, w₂₁]
  | 0 => #v[w₀₁, 0, 0, 0, 0, 0, 0, w₀₁]
  | 1 => #v[w₀₂, 0, 0, 0, 0, 0, 0, w₀₂]
  | 2 => #v[w₁₀, 0, 0, 0, 0, 0, 0, w₁₀]
  | 3 => #v[w₁₁, 0, 0, 0, 0, 0, 0, w₁₁]
  | 4 => #v[w₁₂, 0, 0, 0, 0, 0, 0, w₁₂]
  | 5 => #v[w₂₀, 0, 0, 0, 0, 0, 0, w₂₀]
  | ⊥ => #v[w₂₁, w₂₀, w₁₂, w₁₁, w₁₀, w₀₂, w₀₁, w₀₀]
where
  go (w : UInt8) : Tryte := if w = 0 then ⊥ else if w = 7 then ⊤ else .mk w.toNat
  w₀₀ := W.word[0] >>> 5 -- 000xxxxx
  w₀₁ := W.word[0] >>> 2 &&& 7 -- xxx000xx
  w₀₂ := .add (W.word[0] <<< 1 &&& 7) (W.word[1] >>> 7) -- xxxxxx00 | 0xxxxxxx
  w₁₀ := W.word[1] >>> 4 &&& 7 -- x000xxxx
  w₁₁ := W.word[1] >>> 1 &&& 7 -- xxxx000x
  w₁₂ := .add (W.word[1] <<< 2 &&& 7) (W.word[2] >>> 6) -- xxxxxxx0 | 00xxxxxx
  w₂₀ := W.word[2] >>> 3 &&& 7 -- xx000xxx
  w₂₁ := W.word[2] &&& 7 -- xxxxx000

instance : Coe (Vector Nat 3) TryteWord := ⟨ofVec⟩
instance : Coe TryteWord (Vector Tryte 8) := ⟨toVec⟩

instance : ToString TryteWord where
  toString W := toString W.toVec.toArray

def proj (W : TryteWord) (t : Tryte) := { W with bits := t }

def neg (W : TryteWord) : TryteWord := { W with bits := -W.bits }
instance : Neg TryteWord := ⟨neg⟩

def Boundary (W : TryteWord) : Tryte × Tryte :=
  let w := W.toVec
  (w[0], w[7])

def IsBot (W : TryteWord) : Prop := W.word = #v[0, 0, 0]

instance : DecidablePred IsBot := fun W => by
  rw [IsBot, Vector.eq_mk]
  exact decEq W.word.toArray #[0, 0, 0]

def IsTop (W : TryteWord) : Prop := W.word = #v[255, 255, 255]

instance : DecidablePred IsTop := fun W => by
  rw [IsTop, Vector.eq_mk]
  exact decEq W.word.toArray #[255, 255, 255]

def IsRelative (W : TryteWord) : Prop := W.Boundary.1 = W.Boundary.2

instance : DecidablePred IsRelative := fun W => by
  unfold IsRelative
  obtain ⟨x, y⟩ := W.Boundary
  exact decEq x y

def IsImpartial (W : TryteWord) : Prop := W.Boundary.1 = ⊥ ∧ W.Boundary.2 = 1
instance : DecidablePred IsImpartial := fun _ => by exact instDecidableAnd

def IsPartisan (W : TryteWord) : Prop := W.Boundary.1 = ⊥ ∧ W.Boundary.2 = 2
instance : DecidablePred IsPartisan := fun _ => by exact instDecidableAnd

def IsValid (W : TryteWord) : Prop := W.IsImpartial ∨ W.IsPartisan
instance : DecidablePred IsValid := fun _ => by exact instDecidableOr

def IsAbstract (W : TryteWord) : Prop := W.Boundary.1 = ⊥ ∧ ¬W.IsValid
instance : DecidablePred IsAbstract := fun _ => by exact instDecidableAnd

def IsSurreal (W : TryteWord) : Prop := W.Boundary.1 = 0 ∧ W.Boundary.2 = ⊥
instance : DecidablePred IsSurreal := fun _ => by exact instDecidableAnd

def IsAlien (W : TryteWord) : Prop := W.Boundary.1 ≠ ⊥ ∧ ¬W.IsSurreal
instance : DecidablePred IsAlien := fun _ => by exact instDecidableAnd

end TryteWord

-- indexed by 2-trytes
structure TryteLine where
  bits : Tryte × Tryte
  line : Vector TryteWord 64
deriving Inhabited

namespace TryteLine

def proj (L : TryteLine) (W : TryteWord) := { L with bits := W.Boundary }
def inv (L : TryteLine) : TryteLine := { L with bits := (-L.bits.1, -L.bits.2) }

def neg (L : TryteLine) : TryteLine := { L with line := L.line.map .neg }
instance : Neg TryteLine := ⟨neg⟩

def word (L : TryteLine) : TryteWord :=
  let (x, y) : Fin 64 × Fin 64 := (L.bits.1.toFin8, L.bits.2.toFin8)
  L.line[x + 8 * y]

def IsValid (L : TryteLine) : Prop := ∃ (W : TryteWord), (L.proj W).word.IsValid
def IsAbstract (L : TryteLine) : Prop := ∃ (W : TryteWord), (L.proj W).word.IsAbstract
def IsSurreal (L : TryteLine) : Prop := ∃ (W : TryteWord), (L.proj W).word.IsSurreal

end TryteLine

-- indexed by 4-trytes
structure TryteBall where
  bits : (Tryte × Tryte) × (Tryte × Tryte)
  ball : Vector TryteWord 4096
deriving Inhabited

namespace TryteBall

def proj (B : TryteBall) (W1 W2 : TryteWord) :=
  { B with bits := (W1.Boundary, W2.Boundary) }

def rotate (B : TryteBall) (t : Tryte) : TryteBall :=
  match t with
  | ⊤ => { B with ball := B.ball.map .neg }
  | 0 => { B with bits := B.bits.swap }
  | 1 => { B with bits := (B.bits.1.swap, B.bits.2) }
  | 2 => { B with bits := (B.bits.1, B.bits.2.swap) }
  | 3 => { B with bits := ((B.bits.1.1, B.bits.2.2), (B.bits.2.1, B.bits.1.2)) }
  | 4 => { B with bits := ((B.bits.2.2, B.bits.1.1), (B.bits.2.1, B.bits.1.2)) }
  | 5 => { B with bits := ((B.bits.1.1, B.bits.2.2), (B.bits.1.2, B.bits.2.1)) }
  | ⊥ => { B with bits := ((-B.bits.1.1, -B.bits.1.2), (-B.bits.2.1, -B.bits.2.2)) }

def inv (B : TryteBall) : TryteBall := B.rotate default

def neg (B : TryteBall) : TryteBall := B.rotate ⊤
instance : Neg TryteBall := ⟨neg⟩

def word (B : TryteBall) : TryteWord :=
  let (w, x, y, z) : Fin 4096 × Fin 4096 × Fin 4096 × Fin 4096 :=
    (B.bits.1.1.toFin8, B.bits.1.2.toFin8, B.bits.2.1.toFin8, B.bits.2.2.toFin8)
  B.ball[w + 8 * x + 64 * y + 512 * z]

def IsValid (B : TryteBall) : Prop := ∃ (W1 W2 : TryteWord), (B.proj W1 W2).word.IsValid
def IsAbstract (B : TryteBall) : Prop := ∃ (W1 W2 : TryteWord), (B.proj W1 W2).word.IsAbstract
def IsSurreal (B : TryteBall) : Prop := ∃ (W1 W2 : TryteWord), (B.proj W1 W2).word.IsSurreal

end TryteBall
