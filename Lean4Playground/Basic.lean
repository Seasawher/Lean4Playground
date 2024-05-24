import SciLean.Data.ArrayType.Notation
import SciLean.Data.DataArray

open SciLean

def hello := "world"

def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]

#eval dot ⊞[1.0, 1.0] ⊞[1.0, 1.0]

/--
error: application type mismatch
  dot ⊞[1.0, 1.0] ⊞[1.0, 1.0, 1.0]
argument
  ⊞[1.0, 1.0, 1.0]
has type
  DataArrayN Float (Fin 3) : Type
but is expected to have type
  DataArrayN Float (Fin 2) : Type
-/
#guard_msgs in #eval dot ⊞[1.0,1.0] ⊞[1.0, 1.0, 1.0]

def u :=  ⊞[1.0, 2.0]

#eval u[0]
#eval u[1]

def A := ⊞[1.0, 2.0; 3.0, 4.0]
#eval A[0,1]
#eval A[(0,1)]


def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A[i,j] := x[i]*y[j]
  return A

def digits := ⊞[1.0, 2, 3, 4, 5, 6, 7, 8, 9]

#eval outerProduct digits digits

-- def outerProduct3 {n m : Float} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] := Id.run do
--   let mut A : DataArray Float := ⊞[]
--   A := reserve A (n*m)
--   for (i,j) in (IndexType.univ (Fin n × Fin m)) do
--     A := A.push (x[i]*y[j])
--   return { data:= A, h_size:= sorry }



#check DataArrayN
