universe u v

inductive Form : (u : Nat) → (ε : Type v) → (α : Type u) → Type (max u v + 1) where
  -- short for 'positive'
  | pos : α → Form u ε α
  -- short for 'negative'
  | neg : α → Form u α ε
  -- short for 'connected to'
  | con : (ε → Form (u + 1) ε α) → Form u ε α

instance : Inhabited (Form u ε α) where default := .con .neg

def Form.IsDead (_ : Form u ε α) : Prop := u = 0
def Form.InAtari (_ : Form u ε α) : Prop := u = 1
def Form.InOrbit (_ : Form u ε α) : Prop := u = 2
def Form.IsAlive (_ : Form u ε α) : Prop := u ≥ 3
