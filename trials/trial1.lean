import Lake
import Init
import Mathlib.Data.Real.Basic

#eval 2-1


--Repr : we can use #eval on it
--DecidableEq : allows you to say that two points are equal

axiom Point : Type
axiom Line : Type
structure Line_Segment where
  p : Point
  q : Point




axiom between (a b c: Point) : Prop

axiom lies_on (a : Point) (ln : Line) : Prop

axiom congruence {A : Type} : A → A → Prop 

axiom distance (a b : Point) : ℝ

-- distance axioms
axiom distance_not_neg {p1 p2 : Point} : 0 ≤ distance p1 p2
axiom distance_pos {p1 p2 : Point} : 
  p1 ≠ p2 ↔ 0 < distance p1 p2
axiom distance_zero_segment {p : Point} : distance p p = 0

axiom distance_is_symm : 
  ∀ (p1 p2 : Point), distance p1 p2 = distance p2 p1


axiom distance_between {a b c : Point} : 
  between a b c ↔ distance a b + distance b c = distance a c
axiom between_refl_left (a b : Point) : between a a b
axiom between_refl_right (a b : Point) : between a b b
axiom between_symm {x y z : Point} : 
  between x y z → between z y x


-- Congruency axioms

--- Congruency is equivalence relation

#check Equivalence





--#check cong_is_equiv
axiom CongEquiv {A : Type} : IsEquiv A congruence

lemma CongRefl {A : Type} : ∀ a : A, congruence a a :=
  CongEquiv.refl

lemma CongSymm {A : Type} : 
  ∀ a b : A, congruence a b → congruence b a :=
  CongEquiv.symm

lemma CongTrans {A : Type} : 
  ∀ a b c : A, 
    congruence a b → congruence b c → congruence a c :=
  CongEquiv.trans



--lemma Cong_is_refl (A : Type) : ∀ a ∈ A, @congruence A a a :=
 -- Cong_is_equiv

