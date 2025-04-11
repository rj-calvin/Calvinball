universe u v

inductive Form : (u : Nat) → (ε : Type v) → (α : Type u) → Type (max u v + 1) where
  -- short for 'positive'
  | pos : α → Form u ε α
  -- short for 'negative'
  | neg : α → Form u α ε
  -- short for 'contingent' or 'connection' 
  | con : (ε → Form (u + 1) ε α) → Form u ε α

instance : Inhabited (Form u ε α) where default := .con .neg

namespace Form

variable {α : Type u} {ε : Type v}

def IsDead (_ : Form u ε α) : Prop := u = 0
def InAtari (_ : Form u ε α) : Prop := u = 1
def InOrbit (_ : Form u ε α) : Prop := u = 2
def IsAlive (_ : Form u ε α) : Prop := u ≥ 3

def collapse [Inhabited ε] (fn : ε → α) : Form u ε α → α
| pos a => a
| neg e => fn e
| con x => go 0 x
where
  go (n : Nat) (x : ε → Form (u + n + 1) ε α) : α :=
    if u < n + 1 then
      fn default
    else
      match x default with
      | pos a => a
      | neg e => fn e
      | con y => go (n + 1) y
  termination_by u - n

def signal (m : ε) : Form u ε α → Form (u + 1) ε α
| pos a => pos a
| neg e => neg e
| con x => x m

def extend (fn : ε → Form u ε α) : Form u ε α → Form u ε α
| pos a => pos a
| neg e => fn e
| con x => con (go 0 x)
where
  go (n : Nat) (x : ε → Form (u + n + 1) ε α) (e₀ : ε) : Form (u + 1) ε α :=
    if u < n + 1 then
      neg e₀
    else
      match x e₀ with
      | pos a => pos a
      | neg e => (fn e).signal e₀
      | con y => go (n + 1) y e₀
  termination_by u - n

def entangle : Form u ε α → Form u ε α → Form u ε α
| con x, neg e => con fun _ => x e
| neg e, con y => con fun _ => y e
| _, F => F
