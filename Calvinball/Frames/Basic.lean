universe u v

inductive Frame : (u : Nat) → (ε : Type v) → (α : Type u) → Type (max u v + 1) where
  -- short for 'object'
  | obj : α → Frame u ε α
  -- short for 'reference'
  | ref : ε → Frame u ε α
  -- short for 'relative to'
  | rel : (ε → Frame (u + 1) ε α) → Frame u ε α

instance : Inhabited (Frame u ε α) where default := .rel .ref

def Frame.IsSingular (_ : Frame u ε α) : Prop := u = 0
def Frame.IsSpacial (_ : Frame u ε α) : Prop := u = 6
