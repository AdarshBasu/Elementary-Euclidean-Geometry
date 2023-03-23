-- Contributors : Adarsh, Anurag, Nikhesh, Sainiranjan.

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
| k + 1, ⟨ head :: tail, h ⟩ => by
  have h1 : tail.length = k := by
    simp [List.length_cons] at h
    assumption
  apply Vec.cons head (Vec.ofVector k ⟨ tail, h1⟩ )

/-- Convert a `Vec` to a `Vector` -/
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| 0, _ => ⟨ [], rfl ⟩
| k + 1, Vec.cons head tail => ⟨ head :: (Vec.toVector k tail).val, by
    simp [List.length]; apply (Vec.toVector k tail).property⟩ 

/-- Mapping a `Vec` to a `Vector` and back gives the original `Vec` -/
theorem Vec.ofVector.toVector {α : Type u} (n : ℕ) (v : Vec α n) :
  Vec.ofVector n (Vec.toVector n v) = v := 
  match n with
  | 0 => by
    rw [Vec.ofVector]
    match v with
    | Vec.nil => rfl
  
  | k + 1 => by
    match v with
    | Vec.cons head tail => 
      simp [Vec.ofVector]  
      apply Vec.ofVector.toVector k tail

/-- Mapping a `Vector` to a `Vec` and back gives the original `Vector` -/
theorem Vec.toVector.ofVector {α : Type u} (n : ℕ) (v : Vector α n) :
  Vec.toVector n (Vec.ofVector n v) = v := 
  match n with
  | 0 => by
    rw [Vec.toVector]
    match v with
    | Vector.nil => rfl
  
  | k + 1 => by
    match v with
    | ⟨ head :: tail, h⟩ =>
      simp[toVector]
      simp[ofVector]