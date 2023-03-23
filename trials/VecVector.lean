import Mathlib
import PnP2023.Lec_02_03.InductiveTypes

/-!
Vectors, i.e., lists of a fixed length, can be defined in (at least) two ways. One way is as an indexed inductive type `Vec`, as we saw in lecture and is in the file `InductiveTypes.lean`. 

A different definition is as a subtype `Vector` of lists consisting of those of a fixed length. This is the definition used in `mathlib` and is recalled below.

```lean
/-- `Vector α n` is the type of lists of length `n` with elements of type `α`. -/
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
```

In this lab, you will relate the two definitions by constructing functions that convert between the two definitions and prove that these functions are inverses of each other.
-/
universe u

/-- Convert a `Vector` to a `Vec` -/
def Vec.ofVector {α : Type u}: (n : ℕ) →  Vector α n → Vec α n 
| 0, _ => Vec.nil
| k + 1, Vector.cons head tail => by
  

/-- Convert a `Vec` to a `Vector` 
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| _, _ => sorry --/

def vector1 : Vector ℕ 1 := ⟨ [2] , rfl ⟩
def vector0 : Vector ℕ 0 := ⟨ [], rfl ⟩ 

#eval vector1




/-- Convert a `Vec` to a `Vector` -/
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| 0, _ => ⟨ [], rfl ⟩
| k + 1, Vec.cons head tail => by
  let vectorTail : Vector α k := Vec.toVector k tail
  let ⟨a, b⟩ := vectorTail
  have lem5 : (head :: a).length = k + 1 := by
    simp [List.length, b]
  let vec3 : Vector α (k+1) := ⟨head :: a, lem5⟩
  assumption





/--  Vec.to_list {α : Type u} {n : ℕ} : Vec α n → List α
| Vec.nil => []
| Vec.cons head tail => head :: tail.to_list
-/




-- Mapping a `Vec` to a `Vector` and back gives the original `Vec` -/
theorem Vec.ofVector.toVector {α : Type u} (n : ℕ) (v : Vec α n) :
  Vec.ofVector n (Vec.toVector n v) = v := sorry

/-- Mapping a `Vector` to a `Vec` and back gives the original `Vector` -/
theorem Vec.toVector.ofVector {α : Type u} (n : ℕ) (v : Vector α n) :
  Vec.toVector n (Vec.ofVector n v) = v := sorry