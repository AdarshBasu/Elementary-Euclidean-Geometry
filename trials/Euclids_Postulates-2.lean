import Lake
import Init
import Mathlib.Data.Real.Basic


#eval 1


def And_implies_right (a b : Prop): a ∧ b → a := by
  intro hab
  apply And.left hab
  
/-def Distrubutive (a b c : Prop): a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := by
  apply Iff.intro
  case mp =>
    intro h
    have ha : a := And.left h
    have hborc : b ∨ c := And.right h
    by_cases hc:c
    case inl =>
      have hac : a ∧ c := by apply And.intro ha hc
      apply Or.inr
      assumption
    case inr => 
        by_cases hb : b
        case inl =>
          have hab : a ∧ b := by apply And.intro ha hb
          apply Or.inl
          assumption
        case inr =>-/


theorem FO (A : Type) : ∀ x : A, ∃ y : A , x = y := by
  intro x'
  have lem1 : x' = x' := rfl

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y



def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

-------------------------------------------------------------------------------
axiom Point : Type
-- variable [pts_nonEmpty : Inhabited Point]

axiom Line : Type
axiom lies_on : Point → Line → Prop


axiom congruence : {A : Type} → A → A →  Prop

-- Congruence is equivalence relationship

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


axiom in_between : Point → Point → Point → Prop

structure Segment : Type :=
  p1 : Point
  p2 : Point


axiom distance (Apt Bpt : Point) : ℝ 


-- Distance axioms
axiom dist_is_not_neg (A B : Point): distance A B ≥ 0
axiom dist_same_point (A : Point) : distance A A = 0
axiom dist_geq_0 (A B : Point) : A ≠ B ↔ distance A B >  0
axiom dist_is_symm (A B : Point) : distance A B = distance B A 
axiom dist_tri_ineq (A B C : Point) :
distance A B + distance B C ≥ distance A C



-- Axioms when a point is in between other two
axiom dist_in_between (a b c : Point) (h : in_between a b c) :
distance a b + distance b c = distance a c

axiom between_refl_left (a b : Point) : in_between a a b
axiom between_refl_right (a b : Point) : in_between a b b



--Euclid postulates

--Postulate 1
--Between two points there is an unique line passing through them
axiom Line_of_two_points (A B : Point) (h : A ≠ B): Line --says you get a line from two points
axiom point_contain (A B : Point) (h : A ≠ B) : --says such a line contain both the points
  have l : Line := Line_of_two_points A B h
  lies_on A l ∧ lies_on B l

axiom line_unique (A B: Point) (h : A ≠ B) (l1 l2 : Line): --says such a line is unique
  (lies_on A l1 ∧ lies_on B l1) ∧ (lies_on A l2 ∧ lies_on B l2) → l1 = l2

axiom IsCoincide (l1 l2 : Line) : l1 = l2


--Postulate 2
--A line segment can be extended to get a line
axiom line_from_seg (seg : Segment) : Line --says a you get a line from a segment
axiom contain_end_points (seg : Segment) : --says the end points of the segment lies on the resulting line
  lies_on (seg.p1) (line_from_seg seg) ∧ lies_on (seg.p2) (line_from_seg seg)
/-
theorem line_from_seg_unique (S : Segment) :
let l₁ := line_from_seg S
let l₂ := line_from_seg S
l₁ = l₂ := rfl
  --have lem1 : lies_on S.p1 l₁ ∧ lies_on S.p2 l₂ := contain_end_points S-/

axiom length_of_seg (seg : Segment) : ℝ
axiom Length_of_seg (seg : Segment) : length_of_seg seg = distance seg.p1 seg.p2 



--Postulate 3
--A circle can be drawn from any centre and any radius
structure Circle : Type :=
  centre : Point
  radius : ℝ 

axiom On_circle (A : Point) (C : Circle) :
distance C.centre A = C.radius


/-
def Equi_triangle (A B C : Point) : Prop :=
distance A B = distance A C ∧ distance A C = distance B C
  
  

theorem Elements_th1 (s : Segment) :
∃ C : Point , Equi_triangle (s.p1 s.p2 C) := by
  have c1 : Circle := Circle.mk s.p1 (length_of_seg s)
  have c2 : Circle := Circle.mk s.p2 (length_of_seg s)

-/


--- (c1 : Circle) : c1.centre = segAB.p1 ∧ c1.radius = (distance (segAB.p1 segAB.p2)) → 

--Postulate 4
--All right angles are equal
structure Angle : Type :=
  p1 : Point
  Pivot : Point
  p2 : Point
-- check whether p1 and pivot are different points
axiom reflexAngle : Angle → Angle

axiom mAngle : Angle → ℝ

axiom CompleteAngle (A : Angle): mAngle (reflexAngle A) = 360 - mAngle A

-- properties of Angle
axiom AngleSymm (a b c : Point) : Angle.mk a b c  = Angle.mk c b a

axiom MakingIntPointAngle (a : Point) (A : Angle) : Prop

-- property of "introducing an interior point 'a' within an angle A"
def IntPointAngle (a : Point) (A : Angle) (_ : MakingIntPointAngle a A): Prop :=
  have A1 : Angle := Angle.mk a A.Pivot A.p1
  have A2 : Angle := Angle.mk a A.Pivot A.p2
  (mAngle (A1) < mAngle  A) 
  ∧ (mAngle (A2) < mAngle A) -- strict inequality because of 120


#check IntPointAngle
-- properties of mAngle

axiom mAngle_non_neg (a b c : Point) : mAngle (Angle.mk a b c) ≥ 0 
axiom ZeroAngle (a b c : Point) (hc : in_between a c b): mAngle (Angle.mk a b c) = 0
axiom mAngle_postive (a b c : Point) (hc : ¬ in_between a c b) (ha : ¬ in_between c a b): 
  mAngle (Angle.mk a b c) > 0

axiom mReflexAngle (A : Angle) : mAngle (reflexAngle A) = 360 - mAngle A

-- Angle A as Sum of its constituents
axiom mAngleAdd (a : Point) (A : Angle) (hInt : MakingIntPointAngle a A)(h : IntPointAngle a A hInt) : 
  have A1 : Angle := Angle.mk a A.Pivot A.p1
  have A2 : Angle := Angle.mk a A.Pivot A.p2
  mAngle A = mAngle A1 + mAngle A2

-- Given Angle A, if we introduce segment (a A.Pivot), then
-- the constiuents sum to the whole Angle A. We can obtain the
-- this as a theorem to MakingIntPointAngle, IntPointAngle, mAngleAdd.

-- Postulate 4 says all right angles are equal.
-- We are assigning it a value of 90
axiom isRightAngle (A : Angle): mAngle A = 90
-- straight line is two right angles
axiom StraightAngle (a b c : Point) (h : in_between a b c) : mAngle (Angle.mk a b c) = 180



axiom IsParallel : Line → Line → Prop -- defn of parallel lines
--axiom notPara_Intersect (l1 l2 : Line): IsParallel l1 l2 →  
--∃ c : Point, lies_on c l1 ∧ lies_on c l2 → False

axiom ParaEquiv : IsEquiv Line IsParallel

def somefunc : Nat → Nat → Nat := fun n m ↦ n*m

#eval somefunc 2 3
#check somefunc

lemma Pararefl : ∀ l : Line, IsParallel l l :=
  ParaEquiv.refl

lemma ParaSymm : 
  ∀ l₁ l₂ : Line, 
    IsParallel l₁ l₂ → IsParallel l₂ l₁ :=
      ParaEquiv.symm

lemma ParaTrans : 
  ∀ l₁ l₂ l₃ : Line, 
    IsParallel l₁ l₂ → IsParallel l₂ l₃ → IsParallel l₁ l₃ :=
      ParaEquiv.trans

-- need to take care of the case when l1 = l2 for IsIntersect. 
-- we probably don't need this


-- property of IsIntersect
axiom Intersect_common_point (l1 l2 : Line) (h : ¬ IsParallel l1 l2) : 
  ∃ c : Point, lies_on c l1 ∧ lies_on c l2

-- Unique intersection point of two lines
theorem UniqueIntersectPoint (l1 l2 : Line) (h : ¬ IsParallel l1 l2) :
  lies_on (a : Point) l1 ∧ lies_on a l2 
  →
  lies_on  (b : Point) l1 ∧ lies_on b l2
  →
  a ≠ b → 
  False := by
    intro h1 h2 hab
    have h1l : lies_on a l1 := And.left h1
    have h1r : lies_on a l2 := And.right h1
    have h2l : lies_on b l1 := And.left h2
    have h2r : lies_on b l2 := And.right h2
    let lab := Line_of_two_points a b hab
    have lemlab : lies_on a lab ∧ lies_on b lab := point_contain a b hab
    have lem1 : l1 = lab := by
      apply line_unique a b hab
      apply And.intro
      case a.left => 
        apply And.intro
        case left => assumption
        case right => assumption
      case a.right =>
        assumption
    have lem2 : l2 = lab := by
      apply line_unique a b hab
      apply And.intro
      case a.left =>
        apply And.intro
        case left => assumption
        case right => assumption
      case a.right =>
        assumption
    have lem3 : IsParallel l1 lab := by
      rw [lem1]
      apply Pararefl
    have lem4 : IsParallel lab l2 := by
      rw [lem2]
      apply Pararefl
    have lem5 : IsParallel l1 l2 := by
      apply ParaTrans l1 lab l2 lem3 lem4
    contradiction

-- if a ray stands on a line, then the adjacent angles sum to 180
axiom RSL (a b c o: Point )(l : Line) (R : Segment)(h1 : lies_on a (line_from_seg R))(h2 : lies_on b l) (h3 : lies_on c l)
(h4 : lies_on o l) (h5 : lies_on o (line_from_seg R)):
let AOB := Angle.mk a o b
let AOC := Angle.mk a o c
mAngle (AOB) + mAngle (AOC) = 180  

/-
-- corresponding angles are equal
axiom  COAequal (l1 l2 l3 : Line) (h :  ¬ IsParallel l1 l3) (h' : IsParallel l1 l2 )
(a b p1 p2 p3 p4 : Point) (lies_on a l1)  (lies_on a l3) (lies_on b l2) (lies_on b l3) 
(lies_on p1 l1) (lies_on p2 l1) (lies_on p3 l2) (lies_on p4 l2) :
let P1AB := Angle.mk p1 a b
let P2AB := Angle.mk p2 a b
mAngle (P1AB) = mAngle (P2AB)



-- if sum of adjacent angles is 180, then a line is formed by them
axiom SOA (a b c o : Point) 
let AOC := Angle.mk a o c 
let BOC := Angle.mk b o c
(h : mAngle (AOC) + mAngle (BOC) = 180 ) 
(lies_on a (S1 : Segment)) (lies_on b (S2 : Segment))
(lies_on o (S1 : Segment)) (lies_on o (S2 : Segment))  
(lies_on o  (S3 : Segment )) (lies_on c (S3: Segment))
(l1 : line_from_seg S1) ( l2 : line_from_seg S2) :
l1 = l2 ∧ lies_on a l1 ∧ lies_on b l1 ∧ lies_on o l1
-/


theorem VOAequal (l1 l2 : Line) (h : ¬ IsParallel l1 l2)
(a b c d e : Point ) :
lies_on a l1 ∧ lies_on b l1
→
lies_on c l2 ∧ lies_on d l2
→
lies_on e l1 ∧ lies_on e l2
→
let AED := Angle.mk a e d 
let CEB := Angle.mk c e b
let AEC := Angle.mk a e c 
let BED := Angle.mk b e d 
mAngle (AEC) = mAngle (BED) ∧  mAngle (AED) = mAngle (CEB)
:= by
intro h1 h2 h3 h4 h5
let R := Segment.mk c e
let R' := Segment.mk a e
let R'' := Segment.mk d e

have lem1 : lies_on c (line_from_seg R) := 
  And.left (contain_end_points R)

have lem2 : lies_on b l1 :=
  And.right h1

have lem3 : lies_on a l1 :=
  And.left h1 

have lem4 : lies_on e l1 :=
  And.left h3

have lem5 : lies_on e (line_from_seg R) :=
  And.right (contain_end_points R )  

apply RSL c a b e l1 R lem1 lem2 lem3 lem4 lem5-- mAngle (AEC)+ mAngle (BEC) = 180
apply RSL a d c e l2 R' --  mAngle (AEC) + mAngle (AED) = 180
-- subtract above two → mAngle (BEC) = mAngle (AED)
apply RSL a d c e l2 R' -- mAngle (AEC) + mAngle(AED) = 180
apply RSL a b d e l2 R'' -- mAngle (AED) + mAngle (BED) = 180
-- subtract above two → mAngle (AEC) = mAngle (BED)














