import Calvinball.Trytes.Basic

def MechWord := ReaderT Tryte Part TryteWord
def MechLine := StateT (TryteLine × TryteWord) Part (Tryte × Tryte)
def MechBall := StateCpsT MechWord Part

open Part (assert)

namespace MechWord

def ω : TryteWord := #v[255, 255, 255]
def W₀ : TryteWord := #v[1, 1, 1]
def W₁ : TryteWord := #v[2, 2, 2]
def W₂ : TryteWord := #v[3, 3, 3]
def W₃ : TryteWord := #v[8, 8, 8]
def W₄ : TryteWord := #v[24, 24, 24]
def W₅ : TryteWord := #v[192, 192, 192]
def Ω : TryteWord := default

instance : Inhabited MechWord where
  default
  | ⊤ => assert ω.IsTop fun _ => ω
  | 0 => assert W₀.IsImpartial fun _ => W₀
  | 1 => assert W₁.IsPartisan fun _ => W₁
  | 2 => assert W₂.IsAbstract fun _ => W₂
  | 3 => assert W₃.IsRelative fun _ => W₃
  | 4 => assert W₄.IsRelative fun _ => W₄
  | 5 => assert W₅.IsSurreal fun _ => W₅
  | ⊥ => assert Ω.IsBot fun _ => Ω

end MechWord

instance : OfNat MechWord (n : Nat) := ⟨fun _ => (default : MechWord) (.mk n)⟩

instance [Inhabited α] : Inhabited (MechBall α) where
  default := fun _ m x => do assert (← m default).IsValid fun _ => x default m

instance {n : Nat} [inst : OfNat α n] : OfNat (MechBall α) n where
  ofNat := fun _ m x => do assert (← m (.mk n)).IsAbstract fun _ => x inst.ofNat m

noncomputable instance : Inhabited MechLine where
  default := fun (L, w) => assert L.IsSurreal fun h => (L.bits, L.proj w, -h.choose)

partial def MechWord.outline (m : MechWord) : MechLine := fun (L, w₀) => do
  -- select word using a projection supplied by the given mechanism
  let l := L.proj (← m w₀.bits)
  let w := l.word
  if w.IsRelative then
    -- relative words must be checked for ⊤ / ⊥
    if w.IsBot then
      -- force consistency with ⊥ and return
      assert (w.bits = ⊥) fun _ => (L.bits, l, w)
    else if w.IsTop then
      -- force consistency with ⊤ and return
      assert (w.bits = ⊤) fun _ => (L.bits, l, w)
    else
      outline m (L, w)
  else if w.IsAlien then
    outline m (l, w)
  else
    -- force boundary consistency and return
    assert w.IsSurreal fun _ => (L.bits, l, -w)

def MechBall.lineout (B : MechBall TryteBall) (M1 M2 : MechWord) : Part ((Tryte × Tryte) × TryteLine × TryteWord) :=
  B.runK M2 fun b m => do m.outline (⟨b.word.Boundary, ← go 63 b M1 default⟩, default)
where
  go (n : Fin 64) (b₀ : TryteBall) (m : MechWord) (l : Vector TryteWord 64) : Part (Vector TryteWord 64) := do
    if n = 0 then return l
    else
      let ((_, i), (j, _)) := b₀.bits
      let b := b₀.proj (← m i) (← m j)
      go (n - 1) b m (l.set n b.word)
  termination_by n

def MechBall.extend (f : Tryte → TryteWord → Part TryteWord) (x : α) : MechBall α :=
  fun _ m₀ k => k x $ m₀.bind (flip f)
