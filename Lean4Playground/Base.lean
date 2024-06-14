universe u v

inductive Many (α : Type u) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

variable {α : Type u} {β : Type v}

/-! Many は Functor -/

def Many.map (f : α → β) : Many α → Many β
  | none => none
  | more x xs => Many.more (f x) (fun () => Many.map f <| xs ())

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => (m + 1) * factorial m

@[simp]
theorem Many.map_none (f : α → β) : Many.map f none = none := rfl

instance : Functor Many where
  map := Many.map

instance : LawfulFunctor Many where
  map_const := rfl
  id_map := by
    intro α x
    dsimp [Functor.map]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp [Many.map]
      rw [ih]
  comp_map := by
    intro α β γ g h x
    dsimp [Functor.map]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp [Many.map]
      rw [ih]

/-! Many は Applicative -/

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

@[simp]
theorem Many.one_neq_none (x : α) : (Many.one x = none) ↔ False := by
  constructor
  all_goals
    intro h
    contradiction

def Many.seq (x : Many (α → β)) (f : Unit → Many α) : Many β :=
  match x with
  | .none => .none
  | .more x xs =>
    match f () with
    | .none => .none
    | .more y ys => Many.more (x y) (fun () => Many.seq (xs ()) ys)

@[simp]
theorem Many.seq_right_none (x : Many (α → β)) : Many.seq x (fun _ => none) = none := by
  cases x
  · rfl
  · dsimp [Many.seq]

@[simp]
theorem Many.seq_left_none {α : Type u} {β : Type v} (f : Unit → Many α) :
    Many.seq (none : Many (α → β)) f = none := by
  cases f () <;> dsimp [Many.seq]

instance : Applicative Many where
  pure := Many.one
  seq := Many.seq

def Many.union {α : Type u} : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

@[simp]
theorem Many.union_none {α : Type u} (x : Many α) : Many.union x .none = x := by
  induction x with
  | none => rfl
  | more x xs ih =>
    specialize ih ()
    dsimp [Many.union]
    rw [ih]

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

#print List.bind

instance instMonadMany : Monad Many where
  pure := Many.one
  bind := Many.bind

instance : LawfulFunctor Many where
  map_const := rfl
  id_map := by
    intro α x
    dsimp [Functor.map]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp [Many.map]
      rw [ih]
  comp_map := by
    intro α β γ g h x
    dsimp [Functor.map]
    induction x with
    | none => rfl
    | more x xs ih =>
      specialize ih ()
      dsimp [Many.map]
      rw [ih]

#check bind
