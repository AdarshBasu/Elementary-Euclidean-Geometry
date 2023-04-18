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
  * Prove transitivity of `is_parallel` using Playfair's axiom.
-/

structure IncidenceGeometry /- (Point Line : Type) -/ where
  Point : Type
  Line : Type
  
  /-- The point lies on the given line.-/
  lies_on : Point → Line → Prop

  /-- `in_between a b c` means "`b` is in between `a` & `c`"-/
  in_between : Point → Point → Point → Prop -- is this supposed to be here?
  
  
  -- properties of in_between
  /--`Between_refl_left a b` means "`a` is in between `a` & `b`"-/
  Between_refl_left (a b : Point) : in_between a a b
  
  /--`Between_refl_right a b` means "`b` is in between `a` & `b`"-/
  Between_refl_right (a b : Point) : in_between a b b
  
-- def IncidenceGeometry.Point {P L : Type}(ig : IncidenceGeometry)


-- Enter some description here.
structure EuclidGeometry extends IncidenceGeometry where
  
  -- defining distance
  distance (a b : Point) : ℝ 

  -- distance axioms
  /--distance between two points is non-negative.-/
  dist_is_not_neg (a b : Point): distance a b ≥ 0 
  /--distance from a point to itself is 0.-/
  dist_same_point (a : Point) : distance a a = 0
  /--distance between two distinct points is strictly positive.-/
  dist_geq_0 (a b : Point) : a ≠ b ↔ distance a b > 0
  /--distance from `a` to `b` = distance from `b` to `a`-/
  dist_is_symm (a b : Point) : distance a b = distance b a
  /--Triangle Inequality: `distance a b + distance b c ≥ distance a c`-/
  dist_tri_ineq (a b c : Point) : distance a b + distance b c ≥ distance a c
  /--distance between collinear points `a`, `b`, `c`: `distance a b + distance b c = distance a c`.-/
  dist_in_between (a b c : Point) : 
    in_between a b c ↔ (distance a b + distance b c = distance a c)


  -- Postulate 1
  -- Between two points there is an unique line passing through them
  
  /--Function that takes two distinct points `a` & `b` and gives a line.-/
  Line_of_two_points (a b : Point) (h : a ≠ b): Line 
  /--The line `Line_of_two_points a b` contains the points `a` & `b`.-/
  Point_contain (a b : Point) (h : a ≠ b) : 
    have l : Line := Line_of_two_points a b h
    lies_on a l ∧ lies_on b l
  
  /--A unique line passes through two distinct points `a` & `b`.-/
  Line_unique (A B: Point) (h : A ≠ B) (l1 l2 : Line): 
    (lies_on A l1 ∧ lies_on B l1) ∧ (lies_on A l2 ∧ lies_on B l2) → l1 = l2

  /--Definition of Collinear points `a`, `b`, `c`.-/
  Collinear_point (A B C : Point) (h : A ≠ B): 
    in_between A B C ∨ in_between A C B ∨ in_between C A B 
    → lies_on C (Line_of_two_points A B h)
  
  
  
variable (geom : EuclidGeometry)

/--A line segment is determined by its endpoints. 
segment is a structure that consisting of two endpoints: `p1` & `p2`.-/
structure segment (geom : IncidenceGeometry) where
  p1 : geom.Point
  p2 : geom.Point



instance : Coe EuclidGeometry IncidenceGeometry where
  coe geom := { Point := geom.Point, Line := geom.Line, lies_on := geom.lies_on, in_between := geom.in_between, Between_refl_left := geom.Between_refl_left, Between_refl_right := geom.Between_refl_right}
  

/--Function gives the length of the segment `seg`.-/
def EuclidGeometry.length (seg : segment geom) : ℝ :=
  geom.distance seg.p1 seg.p2




/--`lies_on_segment p seg` means that point `p` lies on segment `seg`.-/
def EuclidGeometry.lies_on_segment (p : geom.Point) (seg : segment geom) : Prop :=
  geom.in_between seg.p1 p seg.p2


-- this defines when a segment lies on a line (use with CAUTION)
/--`segment_in_line seg l` says that all the points of the segment `seg` lie on the line `l`.-/
def EuclidGeometry.segment_in_line
  (seg: segment geom)(l: geom.Line) : Prop :=
  ∀ p: geom.Point, geom.in_between seg.p1 p seg.p2 → geom.lies_on p l



-- this theorem says that the line is unique when the length of the segment is non-zero
/--There is a unique line that contains a line segment of non-zero length.-/
theorem EuclidGeometry.Unique_line_from_segment 
  (seg : segment geom) (h : ¬ seg.p1 = seg.p2) (l1 l2 : geom.Line) : 
  geom.segment_in_line seg l1 ∧ geom.segment_in_line seg l2
  → l1 = l2
  := by
    intro h1
    let ⟨h2, h3⟩ := h1
    apply geom.Line_unique seg.p1 seg.p2 h l1 l2
    apply And.intro
    case left =>
      apply And.intro
      case left =>
        have lem : geom.in_between seg.p1 seg.p1 seg.p2 := 
          geom.Between_refl_left seg.p1 seg.p2
        simp [segment_in_line] at h2
        have lem' : geom.in_between seg.p1 seg.p1 seg.p2 →
          geom.lies_on seg.p1 l1 := by
            simp [h2, lem]
        apply lem'
        assumption
      case right =>
        have lem : geom.in_between seg.p1 seg.p2 seg.p2 := 
          geom.Between_refl_right seg.p1 seg.p2
        simp [segment_in_line] at h2
        have lem' : geom.in_between seg.p1 seg.p2 seg.p2 →
          geom.lies_on seg.p2 l1 := by
            simp [h2, lem]
        apply lem'
        assumption
    case right =>
      apply And.intro
      case left =>
        have lem : geom.in_between seg.p1 seg.p1 seg.p2 := 
          geom.Between_refl_left seg.p1 seg.p2
        simp [segment_in_line] at h3
        have lem' : geom.in_between seg.p1 seg.p1 seg.p2 →
          geom.lies_on seg.p1 l2 := by
            simp [h3, lem]
        apply lem'
        assumption
      case right =>
        have lem : geom.in_between seg.p1 seg.p2 seg.p2 := 
          geom.Between_refl_right seg.p1 seg.p2
        simp [segment_in_line] at h3
        have lem' : geom.in_between seg.p1 seg.p2 seg.p2 →
          geom.lies_on seg.p2 l2 := by
            simp [h3, lem]
        apply lem'
        assumption




/--Definition of Parallel Lines-/
def EuclidGeometry.is_parallel (l1 l2 : geom.Line) : Prop :=
  (l1 = l2) ∨ (∀ a : geom.Point, geom.lies_on a l1 → ¬ geom.lies_on a l2)

        
/--Definition of intersection of lines. Here, we just say: `¬ is_parallel`. -/
def EuclidGeometry.Lines_intersect (l1 l2 : geom.Line) : Prop
  := ¬ is_parallel geom l1 l2


/-- Existence of intersection point for two intersecting lines.-/
theorem EuclidGeometry.Lines_intersect_Point_Exist 
  (l1 l2 : geom.Line) (h : Lines_intersect geom l1 l2) :
  ∃ c : geom.Point, geom.lies_on c l1 ∧ geom.lies_on c l2
  := by
    simp [Lines_intersect, is_parallel] at h
    rw [not_or] at h
    let ⟨_, h2⟩ := h
    simp at h2
    assumption
  

/--`Lines_intersect2 l1 l2 p` states that the lines `l1, l2` 
intersect at the point `p`.-/
def EuclidGeometry.Lines_intersect2
  (l1 l2 : geom.Line) (p : geom.Point) :
  Prop
  := geom.lies_on p l1 ∧ geom.lies_on p l2


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
    simp [Lines_intersect, is_parallel] at h
    rw [not_or] at h
    let ⟨hk, _⟩ := h
    contradiction



/--Existence of intersection point of a line and a segment -/
def EuclidGeometry.Line_intersect_segment
  (seg : segment geom) (l : geom.Line) : Prop := 
  ∃ p : geom.Point, geom.lies_on p l ∧ geom.lies_on_segment p seg

/--`Line_intersect_segment2 seg l p` states that 
line `l` intersects the segment `seg` at point `p`-/
def EuclidGeometry.Line_intersect_segment2
  (seg : segment geom) (l : geom.Line) (p : geom.Point): Prop := 
  geom.lies_on p l ∧ geom.lies_on_segment p seg


-- postulate 3
-- A circle can be constructed with any centre and any radius.
-- this is just the definition of a circle.
/-- Circle is a structure with a point `centre` and positive real `radius`.-/
structure Circle (geom : EuclidGeometry) where
  centre : geom.Point
  radius : ℝ

/--`On_circle p circ` states that the point `p` lies on the circle `circ`.-/
def EuclidGeometry.On_circle (p : geom.Point) (circ : Circle geom) : Prop
  := geom.distance p circ.centre = circ.radius


-- postulate 4

/--Angle is a structure with three points. 
`p1 = a`, `Pivot = o`, `p2 = b` denotes the angle (a o b).-/
structure Angle (geom : EuclidGeometry) where
  p1 : geom.Point
  Pivot : geom.Point
  p2 : geom.Point
  -- prop : ¬ p1 = Pivot ∧ ¬ p2 = Pivot
-- p1 and p2 need to be different from the Pivot

-- TODO: equivalence of angles. Congruence of angles. Same-sidedness with.



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
  geom.Line_intersect_segment (segment.mk p1 p2) l

/--`Same_sided_points p1 p2 l` states that the two points `p1, p2` 
are on the same side of line `l`. Here, it is: `¬ Opp_sided_points p1 p2 l`-/
def EuclidGeometry.Same_sided_points (p1 p2 : geom.Point) (l : geom.Line) : Prop :=
  ¬ geom.Opp_sided_points p1 p2 l
 

-- List of Axioms and Euclid's Postulates
structure Axioms where
  
  /--Euclid Postulate #2: every segment lies on a line.-/
  Post2 (geom : EuclidGeometry) :
    ∀ s : segment geom, ∃ l: geom.Line, geom.segment_in_line s l
    
  /--Line can be obtained from a segment.-/
  Line_from_segment : segment geom → geom.Line

  -- property of Line_from_segment
  /---/
  Line_from_segment_contains_segment (seg : segment geom) :
    geom.segment_in_line seg (Line_from_segment seg)
  
  -- properties of mAngle
  -- TODO: given a real number r, then given a line and a point, there is a line with that angle r on it.
  /--Measure of any angle is non-negative.-/
  mAngle_non_neg (a b c : geom.Point) : 
    mAngle (Angle.mk a b c) ≥ 0

  /--Definition of Zero Angle.-/
  ZeroAngle (a b c : geom.Point) (_ : geom.in_between a c b): 
    mAngle (Angle.mk a b c) = 0

  /--If not a zero angle, then the measure of the angle is positive.-/
  mAngle_postive (a b c : geom.Point) : 
    ¬ geom.in_between a c b → 
    ¬ geom.in_between c a b → 
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
  StraightAngle (a b c : geom.Point) (_ : geom.in_between a b c) :
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
    geom.Line_intersect_segment2 (segment.mk a b) l p1
    →
    geom.Line_intersect_segment2 (segment.mk c d) l p2
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

  /--Playfair's axiom. Equivalent to fifth postulate
  `para_line_playfair p l` is a Line. axiom2 ensures that this is the only line parallel to `l` and passing through `p`-/
  para_line_playfair (p : geom.Point) (l : geom.Line) : geom.Line
  /--states property of the `para_line_playfair p l` that ensures that it is the unique Line parallel to `l` and passing through `p`-/
  axiom2 (p: geom.Point) (l: geom.Line) :
    let m := para_line_playfair p l
    ((geom.lies_on p m) ∧ (geom.is_parallel l m)) ∧ 
    (∀ m' : geom.Line, ((geom.lies_on p m') ∧ (geom.is_parallel l m')) → m = m')

variable {SELF : Axioms geom reflexAngle mAngle}

theorem EuclidGeometry.para_line_playfair_def (p : geom.Point) (l m : geom.Line) (h : geom.lies_on p m) (h' : geom.is_parallel l m) : SELF.para_line_playfair p l = m := by
  have lem1 : (geom.lies_on p m) ∧ (geom.is_parallel l m) := ⟨h, h'⟩
  let m' := SELF.para_line_playfair p l
  have lem2 : m' = m := by
    apply (SELF.axiom2 p l).right
    assumption
  simp [lem2]



-- is_parallel is an equivalence relation on Lines
/--`is_parallel` is reflexive.-/
theorem EuclidGeometry.parallel_refl (l : geom.Line) : 
  is_parallel geom l l 
  := by
    simp [is_parallel]

/-- `is_parallel` is symmetric.-/
theorem EuclidGeometry.Parallel_symm (l1 l2 : geom.Line) : 
  is_parallel geom l1 l2 → is_parallel geom l2 l1 
  := by
    intro h
    simp [is_parallel]
    simp [is_parallel] at h
    apply Or.elim h
    case left =>
      intro h1
      apply Or.inl
      rw [h1]
    case right =>
      intro h2
      apply Or.inr
      intro p hp
      have lem : geom.lies_on p l1 → ¬ geom.lies_on p l2 := by
        apply of_eq_true
        apply eq_true (h2 p)
      by_contra h3
      simp [h3] at lem
      contradiction
  

/--`is_parallel` is transitive.-/
theorem EuclidGeometry.para_trans : ∀ l m n : geom.Line, geom.is_parallel l m → geom.is_parallel m n → geom.is_parallel l n := by
  intro l m n h1 h2
  by_contra h3
  let ⟨p, h4, h5⟩ := geom.Lines_intersect_Point_Exist l n h3
  have h6 : SELF.para_line_playfair p m = l := geom.para_line_playfair_def reflexAngle mAngle p m l h4 (geom.Parallel_symm l m h1)
  have h7 : SELF.para_line_playfair p m = n := geom.para_line_playfair_def reflexAngle mAngle p m n h5 h2
  have h8 : l = n := by
    rw [h6] at h7
    assumption
  rw [h8] at h3
  have h9 : geom.is_parallel n n := geom.parallel_refl n
  contradiction
                       

/--Vertically opposite angles are equal.-/
theorem VOAequal (a b c d o : geom.Point) (SELF : Axioms geom reflexAngle mAngle)
(h1 : ¬a = b)
(h2 : ¬c = d)
(h3 : geom.in_between a o b ∧ geom.in_between c o d)
(_ : ¬geom.is_parallel 
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
  
/--Defination of a triangle. An unique triangle is given by three distinct points-/
structure Triangle (geom : EuclidGeometry) where
  p1 : geom.Point
  p2 : geom.Point
  p3 : geom.Point
  h12 : p1 ≠ p2
  h23 : p2 ≠ p3
  h31 : p3 ≠ p1

/--Two given triangles are equal when all of their corresponding parts are equal-/
def triangles_are_congruent (T1 T2 : Triangle geom) : Prop :=
  geom.distance T1.p1 T1.p2 = geom.distance T2.p1 T2.p2 ∧ 
  geom.distance T1.p2 T1.p3 = geom.distance T2.p2 T2.p3 ∧
  geom.distance T1.p3 T1.p1 = geom.distance T2.p3 T2.p1 ∧
  mAngle (Angle.mk T1.p2 T1.p1 T1.p3) = mAngle (Angle.mk T2.p2 T2.p1 T2.p3) ∧ 
  mAngle (Angle.mk T1.p1 T1.p2 T1.p3) = mAngle (Angle.mk T2.p1 T2.p2 T2.p3) ∧ 
  mAngle (Angle.mk T1.p2 T1.p3 T1.p1) = mAngle (Angle.mk T2.p2 T2.p3 T2.p1)
 

structure triangle_axioms where
  /--SAS congruency property states that two triangles are congurent if two sides and the included angle between them of one triangle are equal to corresponding parts of the other triangle then the two triangles are equal-/
  SAS (T1 T2 : Triangle geom) : 
    (geom.distance T1.p1 T1.p2 = geom.distance T2.p1 T2.p2) 
    → 
    (mAngle (Angle.mk T1.p2 T1.p1 T1.p3) = mAngle (Angle.mk T2.p2 T2.p1 T2.p3)) 
    → 
    (geom.distance T1.p1 T1.p2 = geom.distance T2.p1 T2.p2)
    → 
    triangles_are_congruent geom mAngle T1 T2


/--Definition of interesection of two circles. Two circles are said to be intersectin if `∃p : Point`, `p` lies on both the circles.-/
def EuclidGeometry.circles_intersect (C1 C2 : Circle geom) : Prop :=
  ∃ p : geom.Point, 
  (EuclidGeometry.On_circle geom p C1) ∧ (EuclidGeometry.On_circle geom p C2)


/--Two circles do not intersect when the distance between them is more than the sum of their radii-/
theorem circles_not_intersect (C1 C2 : Circle geom) : 
  ((C1.radius + C2.radius) < geom.distance C1.centre C2.centre)
  → 
  ¬ geom.circles_intersect C1 C2 
  := by
    intro h h'
    let ⟨p, hp1, hp2⟩ := h'
    have lem1 : geom.distance C1.centre p = C1.radius := by
      simp [EuclidGeometry.On_circle] at hp1
      simp [geom.dist_is_symm]
      assumption
    have lem2 : geom.distance p C2.centre = C2.radius := by
      simp [EuclidGeometry.On_circle] at hp2
      assumption
    have lem3 : geom.distance C1.centre p + geom.distance p C2.centre ≥ 
      geom.distance C1.centre C2.centre := geom.dist_tri_ineq C1.centre p C2.centre 
    rw[lem1, lem2] at lem3
    have lem4 : ¬ ((C1.radius + C2.radius) < geom.distance C1.centre C2.centre) := by
      apply not_lt_of_ge
      assumption
    contradiction

/--Two circles do not intersect when the distance between them is less than the difference of their radii. In this this all points of one circle lies inside the other.-/
theorem circles_not_intersect2 (C1 C2 : Circle geom) : 
  C1.radius > geom.distance C1.centre C2.centre + C2.radius
  → 
  ¬ geom.circles_intersect C1 C2 
  := by
    intro h1 h2 
    let ⟨p, hp1, hp2⟩ := h2
    have lem1 : geom.distance C1.centre p = C1.radius := by
      simp [EuclidGeometry.On_circle] at hp1
      simp [geom.dist_is_symm]
      assumption
    have lem2 : geom.distance C2.centre p = C2.radius := by
      simp [EuclidGeometry.On_circle] at hp2
      simp [geom.dist_is_symm]
      assumption
    have lem3 : geom.distance C1.centre C2.centre + geom.distance C2.centre p ≥ 
      geom.distance C1.centre p := geom.dist_tri_ineq C1.centre C2.centre p
    rw[lem1, lem2] at lem3
    have lem4 : ¬ C1.radius > geom.distance C1.centre C2.centre + C2.radius := by
      apply not_lt_of_ge
      assumption
    contradiction


structure circle_axioms where
  -- circles meeting at one point
  circles_one_intersect (C1 C2 : Circle geom) :
    (C1.radius + C2.radius = geom.distance C1.centre C2.centre)
    → 
    ∃! p : geom.Point, geom.On_circle p C1 ∧ geom.On_circle p C2
  -- TODO: given line segment AB, and a real number r less than the length(AB), then there is a point p in the segment AB that is at that distance r

  -- circles intersecting at two points
  circles_two_intersect1 (C1 C2 : Circle geom) :
    C1.radius > C2.radius
    → 
    (C1.radius - C2.radius < geom.distance C1.centre C2.centre)
    →
    (geom.distance C1.centre C2.centre < C1.radius + C2.radius) 
    →
    ∃ p1 p2 : geom.Point, (p1 ≠ p2) ∧ 
      (geom.On_circle p1 C1 ∧ geom.On_circle p1 C2) ∧
      (geom.On_circle p2 C1 ∧ geom.On_circle p2 C2)

  circles_two_intersect2 (C1 C2 : Circle geom) :
    (C1.radius + C2.radius > geom.distance C1.centre C2.centre)
    → ∃ p1 p2 : geom.Point, (p1 ≠ p2) ∧ 
      (geom.On_circle p1 C1 ∧ geom.On_circle p1 C2) ∧
      (geom.On_circle p2 C1 ∧ geom.On_circle p2 C2)

/-First proposition in Euclid's Elements.-/
/--An equilateral triangle can be constructed from a given segment of non-zero length.-/
theorem EuclidGeometry.Eq_tri_from_seg (seg : segment geom) (h : geom.length seg > 0) (ca : circle_axioms geom) : ∃ p : geom.Point, geom.distance p seg.1 = geom.distance seg.1 seg.2 ∧ geom.distance p seg.2 = geom.distance seg.1 seg.2 := by
  let C1 := Circle.mk seg.1 (geom.distance seg.1 seg.2)
  let C2 := Circle.mk seg.2 (geom.distance seg.1 seg.2)
  let lax := ca.circles_two_intersect2 C1 C2 (by
      simp
      simp at h
      unfold length at h
      assumption
       )
  let ⟨p1, _, _, h3, _⟩ := lax
  unfold On_circle at h3
  simp at h3
  use p1
  assumption


