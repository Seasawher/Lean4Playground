universe u v

inductive Many (α : Type u) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

/-! Many は Functor -/

def Many.map {α : Type u} {β : Type v} (f : α → β) : Many α → Many β
  | none => none
  | more x xs => Many.more (f x) (fun () => Many.map f <| xs ())

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

