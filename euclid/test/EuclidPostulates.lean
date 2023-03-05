/-
Project: Euclidean Geometry.
Contributors: Adarsh, Anurag, Nikhesh, Sai Niranjan.
-/

import Lake
import Init
import Mathlib.Data.Real.Basic


set_option autoImplicit false

/-! 
We define basic geometric objects and state Euclid's 5 postulates. 
Convention:
 * Begin variable/theorem names with capital letters.
 * Use underscore between "words" in the variable names.
 * Small letters for Points, Lines, etc.

TODO:
  * Prove equivalence of 5th Postulate and Playfair's axiom.
  * Prove transitivity of `IsParallel` using Playfair's axiom.
  * Show that interior of `Symm_angles` is the same.
-/

structure IncidenceGeometry where
  Point : Type
  Line : Type
  
  /-- The point lies on the given line.-/
  Lies_on : Point → Line → Prop

  /-- ```In_between a b c``` means "`b` is in between `a` & `c`"-/
  In_between : Point → Point → Point → Prop -- is this supposed to be here?
  
  
  -- properties of In_between
  /--`Between_refl_left a b` means "`a` is in between `a` & `b`"-/
  Between_refl_left (a b : Point) : In_between a a b
  
  /--`Between_refl_right a b` means "`b` is in between `a` & `b`"-/
  Between_refl_right (a b : Point) : In_between a b b
  

-- Enter some description here.
structure EuclidGeometry extends IncidenceGeometry where
  
  -- defining Distance
  Distance (a b : Point) : ℝ 

  -- Distance axioms
  /--Distance between two points is non-negative.-/
  Dist_is_not_neg (a b : Point): Distance a b ≥ 0 
  /--Distance from a point to itself is 0.-/
  Dist_same_point (a : Point) : Distance a a = 0
  /--Distance between two distinct points is strictly positive.-/
  Dist_geq_0 (a b : Point) : a ≠ b ↔ Distance a b > 0
  /--Distance from `a` to `b` = Distance from `b` to `a`-/
  Dist_is_symm (a b : Point) : Distance a b = Distance b a
  /--Triangle Inequality: `Distance a b + Distance b c ≥ Distance a c`-/
  Dist_tri_ineq (a b c : Point) : Distance a b + Distance b c ≥ Distance a c
  /--Distance between collinear points `a`, `b`, `c`: `Distance a b + Distance b c = Distance a c`.-/
  Dist_in_between (a b c : Point) (h : In_between a b c) : 
    Distance a b + Distance b c = Distance a c


  -- Postulate 1
  -- Between two points there is an unique line passing through them
  
  /--Function that takes two distinct points `a` & `b` and gives a line.-/
  Line_of_two_points (a b : Point) (h : a ≠ b): Line 
  /--The line `Line_of_two_points a b` contains the points `a` & `b`.-/
  Point_contain (a b : Point) (h : a ≠ b) : 
    have l : Line := Line_of_two_points a b h
    Lies_on a l ∧ Lies_on b l
  
  /--A unique line passes through two distinct points `a` & `b`.-/
  Line_unique (A B: Point) (h : A ≠ B) (l1 l2 : Line): 
    (Lies_on A l1 ∧ Lies_on B l1) ∧ (Lies_on A l2 ∧ Lies_on B l2) → l1 = l2

  /--Definition of Collinear points `a`, `b`, `c`.-/
  Collinear_point (A B C : Point) (h : A ≠ B): 
    In_between A B C ∨ In_between A C B ∨ In_between C A B 
    → Lies_on C (Line_of_two_points A B h)
  
  
  
  
/--A line segment is determined by its endpoints. 
Segment is a structure that consisting of two endpoints: `p1` & `p2`.-/
structure Segment (geom : IncidenceGeometry) where
  p1 : geom.Point
  p2 : geom.Point



instance : Coe EuclidGeometry IncidenceGeometry where
  coe geom := { Point := geom.Point, Line := geom.Line, Lies_on := geom.Lies_on, In_between := geom.In_between, Between_refl_left := geom.Between_refl_left, Between_refl_right := geom.Between_refl_right}
  

/--Function gives the length of the segment `seg`.-/
def EuclidGeometry.length (geom : EuclidGeometry) (seg : Segment geom) : ℝ :=
  geom.Distance seg.p1 seg.p2

variable (geom : EuclidGeometry)


/--`Lies_on_segment p seg` means that point `p` lies on segment `seg`.-/
def EuclidGeometry.Lies_on_segment (p : geom.Point) (seg : Segment geom) : Prop :=
  geom.In_between seg.p1 p seg.p2


-- this defines when a segment lies on a line (use with CAUTION)
/--`Segment_in_line seg l` says that all the points of the segment `seg` lie on the line `l`.-/
def EuclidGeometry.Segment_in_line (geom: EuclidGeometry) 
  (seg: Segment geom)(l: geom.Line) : Prop :=
  ∀ p: geom.Point, geom.In_between seg.p1 p seg.p2 → geom.Lies_on p l



-- this theorem says that the line is unique when the length of the segment is non-zero
/--There is a unique line that contains a line segment of non-zero length.-/
theorem EuclidGeometry.Unique_line_from_segment 
  (seg : Segment geom) (h : ¬ seg.p1 = seg.p2) (l1 l2 : geom.Line) : 
  geom.Segment_in_line seg l1 ∧ geom.Segment_in_line seg l2
  → l1 = l2
  := by
    intro h1
    let ⟨h2, h3⟩ := h1
    apply geom.Line_unique seg.p1 seg.p2 h l1 l2
    apply And.intro
    case left =>
      apply And.intro
      case left =>
        have lem : geom.In_between seg.p1 seg.p1 seg.p2 := 
          geom.Between_refl_left seg.p1 seg.p2
        simp [Segment_in_line] at h2
        have lem' : geom.In_between seg.p1 seg.p1 seg.p2 →
          geom.Lies_on seg.p1 l1 := by
            simp [h2, lem]
        apply lem'
        assumption
      case right =>
        have lem : geom.In_between seg.p1 seg.p2 seg.p2 := 
          geom.Between_refl_right seg.p1 seg.p2
        simp [Segment_in_line] at h2
        have lem' : geom.In_between seg.p1 seg.p2 seg.p2 →
          geom.Lies_on seg.p2 l1 := by
            simp [h2, lem]
        apply lem'
        assumption
    case right =>
      apply And.intro
      case left =>
        have lem : geom.In_between seg.p1 seg.p1 seg.p2 := 
          geom.Between_refl_left seg.p1 seg.p2
        simp [Segment_in_line] at h3
        have lem' : geom.In_between seg.p1 seg.p1 seg.p2 →
          geom.Lies_on seg.p1 l2 := by
            simp [h3, lem]
        apply lem'
        assumption
      case right =>
        have lem : geom.In_between seg.p1 seg.p2 seg.p2 := 
          geom.Between_refl_right seg.p1 seg.p2
        simp [Segment_in_line] at h3
        have lem' : geom.In_between seg.p1 seg.p2 seg.p2 →
          geom.Lies_on seg.p2 l2 := by
            simp [h3, lem]
        apply lem'
        assumption




/--Definition of Parallel Lines-/
def EuclidGeometry.IsParallel (l1 l2 : geom.Line) : Prop :=
  (l1 = l2) ∨ (∀ a : geom.Point, geom.Lies_on a l1 → ¬ geom.Lies_on a l2)


-- IsParallel is an equivalence relation on Lines
/--`IsParallel` is reflexive.-/
theorem EuclidGeometry.Parallel_refl (l : geom.Line) : 
  IsParallel geom l l 
  := by
    simp [IsParallel]

/-- `IsParallel` is symmetric.-/
theorem EuclidGeometry.Parallel_symm (l1 l2 : geom.Line) : 
  IsParallel geom l1 l2 → IsParallel geom l2 l1 
  := by
    intro h
    simp [IsParallel]
    simp [IsParallel] at h
    apply Or.elim h
    case left =>
      intro h1
      apply Or.inl
      rw [h1]
    case right =>
      intro h2
      apply Or.inr
      intro p hp
      have lem : geom.Lies_on p l1 → ¬ geom.Lies_on p l2 := by
        apply of_eq_true
        apply eq_true (h2 p)
      by_contra h3
      simp [h3] at lem
      contradiction
  

-- transitivity : for this we need Playfair's theorem. 
-- Transitivity has not been used in any definition/theorem,
-- so we shall prove it later.
/--`IsParallel` is transitive.-/
theorem EuclidGeometry.Parallel_trans (l1 l2 l3: geom.Line) : 
  IsParallel geom l1 l2 → IsParallel geom l2 l3 → IsParallel geom l1 l3
  := by
    intro h1 h2
    have h1' : IsParallel geom l1 l2 := h1
    have h2' : IsParallel geom l2 l3 := h2

    simp [IsParallel]
    simp [IsParallel] at h1
    simp [IsParallel] at h2
    apply Or.elim h1
    case left =>
      intro h12eq
      apply Or.elim h2
      case left =>
        intro h23eq
        apply Or.inl
        rw [<- h23eq, h12eq]
      case right =>
        intro hk
        rw [<-h12eq] at h2'
        simp [IsParallel] at h2'
        assumption
    case right =>
      intro hk
      apply Or.elim h2
      case left =>
        intro h23eq
        rw [h23eq] at h1'
        simp [IsParallel] at h1'
        assumption
      case right =>
        intro hk1
        by_cases l1 = l3
        case pos =>
          apply Or.inl
          assumption
        case neg =>
          apply Or.inr
          intro p hp
          by_contra hk'
          sorry               -- need to use Playfair's axiom here for this case.

        
        
/--Definition of intersection of lines. Here, we just say: `¬ IsParallel`. -/
def EuclidGeometry.Lines_intersect (l1 l2 : geom.Line) : Prop
  := ¬ IsParallel geom l1 l2


/-- Existence of intersection point for two intersecting lines.-/
theorem EuclidGeometry.Lines_intersect_Point_Exist 
  (l1 l2 : geom.Line) (h : Lines_intersect geom l1 l2) :
  ∃ c : geom.Point, geom.Lies_on c l1 ∧ geom.Lies_on c l2
  := by
    simp [Lines_intersect, IsParallel] at h
    rw [not_or] at h
    let ⟨_, h2⟩ := h
    simp at h2
    assumption
  

/--`Lines_intersect2 l1 l2 p` states that the lines `l1, l2` 
intersect at the point `p`.-/
def EuclidGeometry.Lines_intersect2
  (l1 l2 : geom.Line) (p : geom.Point) :
  Prop
  := geom.Lies_on p l1 ∧ geom.Lies_on p l2


/--Uniqueness of intersection point for two intersecting lines.-/
theorem EuclidGeometry.Lines_intersect_point_unique
  (l1 l2 : geom.Line) (h : Lines_intersect geom l1 l2) (A B : geom.Point) :
  Lines_intersect2 geom l1 l2 A → 
  Lines_intersect2 geom l1 l2 B →
  A = B
  := by
    intro h1 h2
    by_contra hab
    simp [Lines_intersect2] at h1
    let ⟨h1l, h1r⟩ := h1
    simp [Lines_intersect2] at h2
    let ⟨h2l, h2r⟩ := h2
    have lem1 : l1 = l2 := by
      apply geom.Line_unique A B hab
      simp [h1l, h1r, h2l, h2r]
    simp [Lines_intersect, IsParallel] at h
    rw [not_or] at h
    let ⟨hk, _⟩ := h
    contradiction



/--Existence of intersection point of a line and a segment -/
def EuclidGeometry.Line_intersect_segment
  (seg : Segment geom) (l : geom.Line) : Prop := 
  ∃ p : geom.Point, geom.Lies_on p l ∧ geom.Lies_on_segment p seg

/--`Line_intersect_segment2 seg l p` states that 
line `l` intersects the segment `seg` at point `p`-/
def EuclidGeometry.Line_intersect_segment2
  (seg : Segment geom) (l : geom.Line) (p : geom.Point): Prop := 
  geom.Lies_on p l ∧ geom.Lies_on_segment p seg


-- postulate 3
-- A circle can be constructed with any centre and any radius.
-- this is just the definition of a circle.
/-- Circle is a structure with a point `centre` and positive real `radius`.-/
structure Circle (geom : EuclidGeometry) where
  centre : geom.Point
  radius : ℝ

/--`On_circle p circ` states that the point `p` lies on the circle `circ`.-/
def EuclidGeometry.On_circle (p : geom.Point) (circ : Circle geom) : Prop
  := geom.Distance p circ.centre = circ.radius


-- postulate 4

/--Angle is a structure with three points. 
`p1 = a`, `Pivot = o`, `p2 = b` denotes the angle (a o b).-/
structure Angle (geom : EuclidGeometry) where
  p1 : geom.Point
  Pivot : geom.Point
  p2 : geom.Point
-- p1 and p2 need to be different from the Pivot


variable (reflexAngle : Angle geom → Angle geom)

--measure of an angle
variable (mAngle : Angle geom → ℝ)


/--`Int_point_angle a A` states that point `a` is inside angle `A`.-/
def EuclidGeometry.Int_point_angle (a : geom.Point) (A : Angle geom) : Prop :=
  let A1 : Angle geom := Angle.mk a A.Pivot A.p1
  let A2 : Angle geom := Angle.mk a A.Pivot A.p2
  (mAngle (A1) < mAngle  A) ∧ (mAngle (A2) < mAngle A) -- strict inequality because of 120  


-- we need to write that Int_point_angle for angles AOB and BOA are the same

-- Postulate 4 says all right angles are equal.
-- We are assigning it a value of 90
/--Define a property called `Is_right_angle A` which states that 
`A` is a right angle and its measure is 90.-/
def EuclidGeometry.Is_right_angle (A : Angle geom): Prop := mAngle A = 90


-- Postulate 5

/--`Opp_sided_points p1 p2 l` states that the two points `p1, p2` 
are on opposite sides of line `l`.-/
def EuclidGeometry.Opp_sided_points (p1 p2 : geom.Point) (l : geom.Line) : Prop :=
  geom.Line_intersect_segment (Segment.mk p1 p2) l

/--`Same_sided_points p1 p2 l` states that the two points `p1, p2` 
are on the same side of line `l`. Here, it is: `¬ Opp_sided_points p1 p2 l`-/
def EuclidGeometry.Same_sided_points (p1 p2 : geom.Point) (l : geom.Line) : Prop :=
  ¬ geom.Opp_sided_points p1 p2 l



-- List of Axioms and Euclid's Postulates
structure Axioms where
  
  /--Euclid Postulate #2: every segment lies on a line.-/
  Post2 (geom : EuclidGeometry) :
    ∀ s : Segment geom, ∃ l: geom.Line, geom.Segment_in_line s l
    
  /--Line can be obtained from a segment.-/
  Line_from_segment : Segment geom → geom.Line

  -- property of Line_from_segment
  /---/
  Line_from_segment_contains_segment (seg : Segment geom) :
    geom.Segment_in_line seg (Line_from_segment seg)
  
  -- properties of mAngle
  /--Measure of any angle is non-negative.-/
  mAngle_non_neg (a b c : geom.Point) : 
    mAngle (Angle.mk a b c) ≥ 0

  /--Definition of Zero Angle.-/
  ZeroAngle (a b c : geom.Point) (_ : geom.In_between a c b): 
    mAngle (Angle.mk a b c) = 0

  /--If not a zero angle, then the measure of the angle is positive.-/
  mAngle_postive (a b c : geom.Point) : 
    ¬ geom.In_between a c b → 
    ¬ geom.In_between c a b → 
    mAngle (Angle.mk a b c) > 0
  
  /--`mReflexAngle A` returns the measure of the reflex angle of angle `A`.-/
  mReflexAngle (A : Angle geom) : 
    mAngle (reflexAngle A) = 360 - mAngle A
  
  
  
  /-- Angle `A` as sum of its constituents.
  For `mAngle_add a A h`, we have:

  `have A1 : Angle geom := Angle.mk a A.Pivot A.p1`

  `have A2 : Angle geom := Angle.mk a A.Pivot A.p2`
  
  then 
  `mAngle A = mAngle A1 + mAngle A2`-/
  mAngle_add (a : geom.Point) (A : Angle geom) 
    (_ : EuclidGeometry.Int_point_angle geom mAngle a A) :
    have A1 : Angle geom := Angle.mk a A.Pivot A.p1
    have A2 : Angle geom := Angle.mk a A.Pivot A.p2
    mAngle A = mAngle A1 + mAngle A2
  
  /--The measure of a straight angle is 180.-/
  StraightAngle (a b c : geom.Point) (_ : geom.In_between a b c) :
    mAngle (Angle.mk a b c) = 180

  -- equality of measure of "symmetric" angles: e.g. Angle AOB = Angle BOA
  -- can't write directly that they are equal as they are different structures "entrywise".
  -- we need to also mention that their interior points are equal.
  /--`Symm_angles (a o b)` states that:
  
  `mAngle (Angle (a o b)) = mAngle (Angle (b o a))`.-/
  Symm_angles (a o b : geom.Point): 
    mAngle (Angle.mk a o b) = mAngle (Angle.mk b o a)


  -- Statement of Postulate 5: 
  -- Let line segment AB and CD be intersected by 
  -- line l at points p1 and p2 respectively.
  -- Let A and C be same-sided wrt l.
  -- Let mAngle(A p1 p2) + mAngle(C p2 p1) < 180.
  -- Then there exists a point p such that
  -- line from AB and CD intersect at p
  -- and p is same-sided as A wrt to line l.
  /--Euclid's Postulate #5.-/
  Post5 (a b c d p1 p2 : geom.Point) (l : geom.Line)
    (hab : ¬ a = b) (hcd : ¬ c = d) :
    geom.Line_intersect_segment2 (Segment.mk a b) l p1
    →
    geom.Line_intersect_segment2 (Segment.mk c d) l p2
    → 
    geom.Same_sided_points a c l
    → 
    mAngle (Angle.mk a p1 p2) + mAngle (Angle.mk c p2 p1) < 180
    → 
    ∃ p : geom.Point, 
    geom.Lines_intersect2 
    (geom.Line_of_two_points a b hab) (geom.Line_of_two_points c d hcd) p
    ∧ 
    geom.Same_sided_points p a l


/--Vertically opposite angles are equal.-/
theorem VOAequal (a b c d o : geom.Point) (SELF : Axioms geom reflexAngle mAngle)
(h1 : ¬a = b)
(h2 : ¬c = d)
(h3 : geom.In_between a o b ∧ geom.In_between c o d)
(_ : ¬geom.IsParallel 
  (geom.Line_of_two_points a b h1) 
  (geom.Line_of_two_points c d h2)) 
(h5: geom.Int_point_angle mAngle c (Angle.mk a o b)) 
(h6: geom.Int_point_angle mAngle a (Angle.mk c o d)):
let COB := Angle.mk c o b
let AOD := Angle.mk a o d
mAngle (COB) = mAngle (AOD)
:= by 
  let COA := Angle.mk c o a
  let AOC := Angle.mk a o c
  let AOD := Angle.mk a o d 
  let AOB := Angle.mk a o b
  let COD := Angle.mk c o d
  let COB := Angle.mk c o b
  have lem1 : mAngle (AOB) = 180 := Axioms.StraightAngle SELF a o b (And.left h3)
  have lem2 : mAngle (COD) = 180 := Axioms.StraightAngle SELF c o d (And.right h3)
  have lem3 : mAngle (AOB) = mAngle (COA) + mAngle (COB) := 
    Axioms.mAngle_add SELF c AOB h5
  have lem4 : mAngle (COD) = mAngle (AOC) + mAngle (AOD) := 
    Axioms.mAngle_add SELF a COD h6
  have lem5 : mAngle COA = mAngle AOC := by 
    apply Axioms.Symm_angles SELF
  have lem6 : mAngle (COA) + mAngle (COB) = mAngle (AOC) + mAngle (AOD) := by
    rw [<-lem3, <-lem4, lem1, lem2]
  rw [lem5] at lem6
  simp [add_left_cancel] at lem6
  assumption
  

