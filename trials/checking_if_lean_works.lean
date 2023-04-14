import Lake
import Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector

#eval 1

/-!
# Indexed inductive type

We define types `Vec α n` for `α : Type u` and `n: ℕ` with terms of `Vec α n` n-tuples in `α`.

* `α` will be a parameter.
* `n` will be an index.
-/

inductive Vec (α : Type u) : 
            ℕ → Type (u + 1) where
| nil : Vec α 0
| cons : {n : ℕ} →  
  (head : α) → (tail : Vec α n) → Vec α (n + 1)  

example : Vec ℕ 0 := Vec.nil

example : Vec ℕ 1 := Vec.cons 3 (Vec.nil)

#check List

def Vec.to_list {α : Type u} {n : ℕ} : Vec α n → List α
| Vec.nil => []
| Vec.cons head tail => head :: tail.to_list




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

#print Vec.ofVector

/-- Convert a `Vec` to a `Vector` 
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| _, _ => sorry --/

def vector1 : Vector ℕ 1 := ⟨ [2] , rfl ⟩
def vector0 : Vector ℕ 0 := ⟨ [], rfl ⟩ 

#eval vector1




/-- Convert a `Vec` to a `Vector` -/
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| 0, _ => ⟨ [], rfl ⟩
| k + 1, Vec.cons head tail => ⟨ head :: (Vec.toVector k tail).val, by
    simp [List.length]; apply (Vec.toVector k tail).property⟩ 
  -- by
  -- let vectorTail : Vector α k := Vec.toVector k tail
  -- let ⟨Ltail, h⟩ := vectorTail

  -- ------------------------
  -- --have lem1: Ltail = vectorTail.1 := by
  -- ------------------------
  -- have lem5 : (head :: Ltail).length = k + 1 := by
  --   simp [List.length, h]
  -- let vec3 : Vector α (k+1) := ⟨head :: Ltail, lem5⟩
  -- apply vec3

-- def Vec.toVector2 {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
-- | 0, _ => ⟨ [], rfl ⟩
-- | k + 1, Vec.cons head tail => by
--   let vectorTail : Vector α k := Vec.toVector2 k tail
--   let ⟨Ltail, h⟩ := vectorTail
--   ------------------------
--   have lem1: Ltail = vectorTail.1 := by
    

--   ------------------------
--   have lem5 : (head :: Ltail).length = k + 1 := by
--     simp [List.length, h]
--   let vec3 : Vector α (k+1) := ⟨head :: Ltail, lem5⟩
--   apply vec3

-- #print Vec.toVector2

def V : Vec ℕ 3  := Vec.cons 1 (Vec.cons 3 (Vec.cons 2 Vec.nil))
#check (Vec.toVector 3 V).2

def vec : Vector ℕ 3 := ⟨[1,5,3],rfl⟩ 

#check vec
#check vec.2


/--  Vec.to_list {α : Type u} {n : ℕ} : Vec α n → List α
| Vec.nil => []
| Vec.cons head tail => head :: tail.to_list
-/
def p : Prop := (1 = 1) ∧ (2 = 2)
#check p
theorem A (h : p): 1 = 1 := by
  let ⟨ha, _⟩ := h
  apply ha

-- Mapping a `Vec` to a `Vector` and back gives the original `Vec` -/
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


#print Vec.ofVector.toVector
      -- let Lhead := (Vec.toVector (k + 1) (Vec.cons head tail)).head
      -- let Ltail := (Vec.toVector (k + 1) (Vec.cons head tail)).tail
      -- let h := (Vec.toVector (k + 1) (Vec.cons head tail)).2
      
      


      -- have lem1 : Lhead :: Ltail = head :: (Vec.toVector k tail).val := by
      --   simp [Vec.toVector]
      --   apply And.intro
      --   case left =>



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
      simp only [ofVector]
      
      -- have lem1 : head ::
      --   (toVector (k + 0 + 0) 
      --   (ofVector (k + 0) 
      --   { val := tail, property := (h1 : List.length tail = Nat.add k 0) })).val = 
      --   head :: tail := 
          
#check Vec.ofVector
#print Vec.toVector.ofVector
      

    





    



-- /-- Mapping a `Vector` to a `Vec` and back gives the original `Vector` -/
-- theorem Vec.toVector.ofVector2 {α : Type u} (n : ℕ) (v : Vector α n) :
--   Vec.toVector n (Vec.ofVector n v) = v :=
--    match n with
--   | 0 => by
--     rw [Vec.toVector]
--     match v with
--     | Vector.nil => rfl
  
--   | k + 1 => by 
--     match v with
--     | ⟨head :: tail, h⟩ =>
--       simp [Vec.toVector]
      
--       have lem1 : tail.length = k := by
--         simp [List.length_cons] at h
--         assumption

--       --apply Vec.toVector.ofVector k ⟨tail, lem1⟩
      
--       have lemt : (toVector k (Vec.ofVector k ⟨tail, lem1⟩)) = ⟨tail, lem1⟩ := by
--         apply Vec.toVector.ofVector k ⟨tail, lem1⟩
      
--       simp only [lemt]
--       -- head :: ↑(toVector (k + 0 + 0) (Vec.ofVector (k + 0) { val := tail, property := (_ : List.length tail = Nat.add k 0) }))
      
      
--       let vecTail : Vector α k := ⟨tail, lem1⟩ 


--       have lem2_val : 
--       head :: (Vec.toVector k (Vec.ofVector k vecTail)).val = 
--       head :: tail := by
--         simp
--         simp [Vec.toVector.ofVector, lem1]
      

      
--       simp [lem2_val]


--       have lem3 : (_ :
--         List.length
--             (head ::
--               ↑(toVector (Nat.add (k + 0) 0)
--                   (Vec.ofVector (k + 0) { val := tail, property := (_ : List.length tail = Nat.add k 0) }))) =
--           Nat.add (k + 0) 0 + 1
          
      

-- theorem Vec.toVector.ofVector2 {α : Type u} (n : ℕ) (v : Vector α n) :
--   Vec.toVector n (Vec.ofVector n v) = v := by
--     induction n
--     case zero =>
--       rw [Vec.toVector]
--       match v with
--       | Vector.nil => rfl
--     case succ =>
--       apply n_ih✝
--       simp [Vec.toVector]
    

      --apply Vec.toVector.ofVector k --⟨tail, lem1⟩ 

/-{
    val :=
      head ::
        ↑(toVector k
            (Vec.ofVector k { val := tail, property := (_ : List.length tail = k })),
    property :=
      (_ :
        List.length
            (head ::
              ↑(toVector k)
                  (Vec.ofVector k { val := tail, property := (_ : List.length tail = k) }))) =
          k + 1) } =
  { val := head :: tail, property := h }-/




/-(match
    toVector k (Vec.ofVector k { val := tail, property := (_ : List.length tail = k) }) with
  | { val := Ltail, property := h } =>
    { val := head :: Ltail, property := (_ : List.length Ltail= k) }) =
  { val := head :: tail, property := h }-/














#eval 1


#check Subtype
#check Subtype.mk -- (val : α) → p val → Subtype p
#check Subtype.property

universe u

inductive InfiniteTree (α : Type u) where
| leaf (label: α) : InfiniteTree α
| node : (ℕ → InfiniteTree α) → InfiniteTree α

inductive FiniteTree (α : Type u) where
| leaf (label: α) : FiniteTree α
| node : (List <| FiniteTree α)  → FiniteTree α



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






-------------------------------------------------------------------------------
variable (Point : Type)
variable [pts_nonEmpty : Inhabited Point]

variable (Line : Type)
variable (lies_on : Point → Line → Prop)

def samePoint(p₁ p₂: Point) := p₁ = p₂

def some_point : Point := default

#check some_point

structure IncidenceGeometry where
  Line : Type
  Point : Type
  lies_on : Point → Line → Prop

def intersect {geom : IncidenceGeometry}(l₁ l₂ : geom.Line) : Prop :=
  ∃p : geom.Point, geom.lies_on p l₁ ∧ geom.lies_on p l₂

def intersect_on_pair {geom : IncidenceGeometry}(l₁ l₂ : geom.Line) : Prop :=
  ∃p₁ p₂ : geom.Point, geom.lies_on p₁ l₁ ∧ geom.lies_on p₁ l₂ ∧ 
            geom.lies_on p₂ l₁ ∧ geom.lies_on p₂ l₂ ∧ p₁ ≠ p₂

variable (congruence : {A : Type} → A → A →  Prop)

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
  (lies_on A l1 ∧ lies_on B l2) ∧ (lies_on A l2 ∧ lies_on B l2) → l1 = l2

axiom IsCoincide (l1 l2 : Line) : l1 = l2


--Postulate 2
--A line segment can be extended to get a line
axiom line_from_seg (seg : Segment) : Line --says a you get a line from a segment
axiom contain_end_points (seg : Segment) : --says the end points of the segment lies on the resulting line
  lies_on (seg.p1) (line_from_seg seg) ∧ lies_on (seg.p2) (line_from_seg seg)

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

-- properties of Angle
axiom AngleSymm (a b c : Point) : Angle.mk a b c = Angle.mk c b a

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
-- TODO: straight line is two right angles
axiom StraightAngle (a b c : Point) (h : in_between a b c) : mAngle (Angle.mk a b c) = 180


-- Postulate 5
-- If a straight line falling on two straight lines makes the interior
-- angles on the same side of it taken together less than two right angles, then the
-- two straight lines, if produced indefinitely, meet on that side on which the sum of
-- angles is less than two right angles.

axiom IsParallel (l1 l2 : Line): Prop -- defn of parallel lines
axiom IsParrallel_isequiv : sorry

-- need to take care of the case when l1 = l2 for IsIntersect. 
-- we probably don't need this


-- property of IsIntersect
axiom PointFromIntersect (l1 l2 : Line) (h : ¬ IsParallel l1 l2) : 
  ∃ c : Point, lies_on c l1 ∧ lies_on c l2

-- Unique intersection point of two lines
theorem UniqueIntersectPoint (l1 l2 : Line) (h1 : l1 ≠ l2) (h2 : ¬ IsParallel l1 l2 h1) : 
  lies_on (a : Point) l1 ∧ lies_on a l2
  →
  lies_on  (b : Point) l1 ∧ lies_on b l2
  →
  a = b
  := sorry 


-/
-- Towards same-sided-ness
-- entire segment is on the line
/-def SegmentOnLine (A : Segment) (l : Line) : Prop := 
  lies_on A.p1 l ∧ lies_on A.p2 l-/

-- points on a segment
def PointOnSegment (a : Point) (A : Segment) : Prop :=
  in_between A.p1 a A.p2

axiom SegLineIntersect (A : Segment) (l : Line) (h : ¬ SegmentOnLine A l) 
  : Prop
-- need to introduce property of SegLineIntersect
-- have not accounted for the case where segment "stands on" the line


-- Points on the same side of a line segment
axiom SameSidedPoints (a b : Point) (l : Line) 
  (h1 : ¬ SegmentOnLine (Segment.mk a b) l) 
  (h2 : ¬ SegLineIntersect (Segment.mk a b) l h1) 
  : Prop


axiom IntersectingLines (A B C : Segment) 
  (h1 : ¬ SegmentOnLine (Segment.mk A.p1 B.p1) (line_from_seg C))
  (h2 : ¬ SegLineIntersect (Segment.mk A.p1 B.p1) (line_from_seg C) h1)
  : 
  SameSidedPoints (A.p1) (B.p1) (line_from_seg C) h1 h2
  →  

  /-
  → 
  (in_between A.p1 C.p1 A.p2) ∧ (in_between B.p1 C.p2 B.p2) 
  -- what about C.p1 = A.p1? is this not taken care of by SegLineIntersect?
  → -/
--  (need to bring in "same-sided-ness")













