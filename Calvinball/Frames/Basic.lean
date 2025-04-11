universe u v

inductive Frame : (u : Nat) → (ε : Type v) → (α : Type u) → Type (max u v + 1) where
  -- short for 'object'
  | obj : α → Frame u ε α
  -- short for 'reference'
  | ref : ε → Frame u ε α
  -- short for 'relative'
  | rel : (ε → Frame (u + 1) ε α) → Frame u ε α

instance : Inhabited (Frame u ε α) where default := .rel .ref

namespace Frame

variable {α : Type u} {ε : Type v}

def IsSingular (_ : Frame u ε α) : Prop := u = 0
-- spacial frames support six degrees-of-freedom
def IsSpacial (_ : Frame u ε α) : Prop := u = 6

def collapse [Inhabited ε] (fn : ε → α) : Frame u ε α → α
| obj a => a
| ref e => fn e
| rel x => go 0 x
where
  go (n : Nat) (x : ε → Frame (u + n + 1) ε α) : α :=
    if u < n + 1 then
      fn default
    else
      match x default with
      | obj a => a
      | ref e => fn e
      | rel y => go (n + 1) y
  termination_by u - n

def signal (m : ε) : Frame u ε α → Frame (u + 1) ε α
| obj a => obj a
| ref e => ref e
| rel x => x m

def extend (fn : ε → Frame u ε α) : Frame u ε α → Frame u ε α
| obj a => obj a
| ref e => fn e
| rel x => rel (go 0 x)
where
  go (n : Nat) (x : ε → Frame (u + n + 1) ε α) (e₀ : ε) : Frame (u + 1) ε α :=
    if u < n + 1 then
      ref e₀
    else
      match x e₀ with
      | obj a => obj a
      | ref e => (fn e).signal e₀
      | rel y => go (n + 1) y e₀
  termination_by u - n

def entangle : Frame u ε α → Frame u ε α → Frame u ε α
| rel x, ref e => rel fun _ => x e
| ref e, rel y => rel fun _ => y e
| _, F => F
