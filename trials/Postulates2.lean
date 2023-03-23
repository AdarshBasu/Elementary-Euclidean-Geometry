import Lake
import Init
import Mathlib.Data.Real.Basic


#eval 1


set_option autoImplicit false

-- All of Incidence Geometry
structure IncidenceGeometry where
  Point : Type
  Line : Type
 
  lies_on : Point → Line → Prop
  in_between : Point → Point → Point → Prop -- is this supposed to be here?
  -- properties of in_between
  between_refl_left (a b : Point) : in_between a a b
  between_refl_right (a b : Point) : in_between a b b
  
--def segme (geom : IncidenceGeometry) : Type := geom.Point × geom.Point

--#check segme

--def somseg (geom : IncidenceGeometry) (A B : geom.Point) : segme geom := (segme geom).mk A B 

structure EuclidGeometry extends IncidenceGeometry where
  --Segment : Type := Point × Point
  --contain_end_points (seg : Segment) : --says the end points of the segment lies on the resulting line
    --lies_on (seg.1) (line_from_seg seg) ∧ lies_on (seg.2) (line_from_seg seg)
  

  --som (a b : Point) : Segment := (a,b)
  
  -- defining distance
  distance (Apt Bpt : Point) : ℝ 
  --distance definition
  dist_is_not_neg (A B : Point): distance A B ≥ 0 
  dist_same_point (A : Point) : distance A A = 0
  dist_geq_0 (A B : Point) : A ≠ B ↔ distance A B >  0
  dist_is_symm (A B : Point) : distance A B = distance B A
  dist_tri_ineq (A B C : Point) : distance A B + distance B C ≥ distance A C
  -- distance axioms when a point is in between other two
  dist_in_between (a b c : Point) (h : in_between a b c) : 
    distance a b + distance b c = distance a c


  -- Postulate 1
  -- Between two points there is an unique line passing through them
  
  Line_of_two_points (A B : Point) (h : A ≠ B): Line -- from two points we get a line (it may not be unique)
  point_contain (A B : Point) (h : A ≠ B) : --says such a line contain both the points
    have l : Line := Line_of_two_points A B h
    lies_on A l ∧ lies_on B l
  
  line_unique (A B: Point) (h : A ≠ B) (l1 l2 : Line): --says such a line is unique
  (lies_on A l1 ∧ lies_on B l1) ∧ (lies_on A l2 ∧ lies_on B l2) → l1 = l2

  Collinear_point (A B C : Point) (h : A ≠ B): 
    in_between A B C ∨ in_between A C B ∨ in_between C A B 
    → lies_on C (Line_of_two_points A B h)
  


  -- end of Postulate 1
  
  -- Postulate 2
  -- A line segment can be extended to get a line
  
  --line_from_seg (seg : Segment) : Line --says a you get a line from a segment

structure Segment (geom : IncidenceGeometry) where
  p1 : geom.Point
  p2 : geom.Point

instance : Coe EuclidGeometry IncidenceGeometry where
  coe geom := { Point := geom.Point, Line := geom.Line, lies_on := geom.lies_on, in_between := geom.in_between, between_refl_left := geom.between_refl_left, between_refl_right := geom.between_refl_right }



def EuclidGeometry.length (geom : EuclidGeometry) (s : Segment geom) : ℝ :=
  geom.distance s.p1 s.p2



-- def EuclidGeometry.point_on_segment (geom : EuclidGeometry) (s : Segment geom) (p : geom.Point) : Prop :=
--   geom.in_between s.p1 p s.p2


variable (geom : EuclidGeometry)

-- this says that there is 

-- points in between the segment endpoints lie on the segment
def EuclidGeometry.lies_on_segment (p : geom.Point) (seg : Segment geom) : Prop :=
  geom.in_between seg.p1 p seg.p2

-- this defines when a segment lies on a line (use with CAUTION)
def EuclidGeometry.segment_in_line (geom: EuclidGeometry) 
  (s: Segment geom)(l: geom.Line) : Prop :=
  ∀ p: geom.Point, geom.in_between s.p1 p s.p2 → geom.lies_on p l


-- this says that every segment lies on a line
def EuclidGeometry.Post2 (geom : EuclidGeometry) : Prop := 
  ∀ s : Segment geom, ∃ l: geom.Line, geom.segment_in_line s l


-- Line obtained from a segment
variable (Line_from_segment : Segment geom → geom.Line)

-- property of Line_from_segment
def EuclidGeometry.Line_from_segment_contains_segment (seg : Segment geom) : Prop :=
  geom.segment_in_line seg (Line_from_segment seg)


-- this theorem says that the line is unique when the length of the segment is non-zero
theorem EuclidGeometry.Unique_line_from_segment 
  (seg : Segment geom) (h : ¬ seg.p1 = seg.p2) (l1 l2 : geom.Line) : 
  geom.segment_in_line seg l1 ∧ geom.segment_in_line seg l2
  → l1 = l2
  := by
    intro h1
    let ⟨h2, h3⟩ := h1
    apply geom.line_unique seg.p1 seg.p2 h l1 l2
    apply And.intro
    case left =>
      apply And.intro
      case left =>
        have lem : geom.in_between seg.p1 seg.p1 seg.p2 := 
          geom.between_refl_left seg.p1 seg.p2
        simp [segment_in_line] at h2
        have lem' : geom.in_between seg.p1 seg.p1 seg.p2 →
          geom.lies_on seg.p1 l1 := by
            simp [h2, lem]
        apply lem'
        assumption
      case right =>
        have lem : geom.in_between seg.p1 seg.p2 seg.p2 := 
          geom.between_refl_right seg.p1 seg.p2
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
          geom.between_refl_left seg.p1 seg.p2
        simp [segment_in_line] at h3
        have lem' : geom.in_between seg.p1 seg.p1 seg.p2 →
          geom.lies_on seg.p1 l2 := by
            simp [h3, lem]
        apply lem'
        assumption
      case right =>
        have lem : geom.in_between seg.p1 seg.p2 seg.p2 := 
          geom.between_refl_right seg.p1 seg.p2
        simp [segment_in_line] at h3
        have lem' : geom.in_between seg.p1 seg.p2 seg.p2 →
          geom.lies_on seg.p2 l2 := by
            simp [h3, lem]
        apply lem'
        assumption


        



-- defining parallel lines
def EuclidGeometry.IsParallel (l1 l2 : geom.Line) : Prop :=
  (l1 = l2) ∨ (∀ a : geom.Point, geom.lies_on a l1 → ¬ geom.lies_on a l2)


-- IsParallel is an equivalence relation on Lines
theorem EuclidGeometry.Parallel_refl (l : geom.Line) : 
  IsParallel geom l l 
  := by
    simp [IsParallel]


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
      have lem : geom.lies_on p l1 → ¬ geom.lies_on p l2 := by
        apply of_eq_true
        apply eq_true (h2 p)
      by_contra h3
      simp [h3] at lem
      contradiction
  





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

        
        
        







-- defining intersection of lines (not segments)  
def EuclidGeometry.Lines_Intersect (l1 l2 : geom.Line) : Prop
  := ¬ IsParallel geom l1 l2


-- unique/existence(?) intersection point for two intersecting lines
theorem EuclidGeometry.Lines_Intersect_Point_Exist 
  (l1 l2 : geom.Line) (h : Lines_Intersect geom l1 l2) :
  ∃ c : geom.Point, geom.lies_on c l1 ∧ geom.lies_on c l2
  := by
    simp [Lines_Intersect, IsParallel] at h
    rw [not_or] at h
    let ⟨_, h2⟩ := h
    simp at h2
    assumption
  





-- "extracting" point of intersection (use with CAUTION. point p can be any point whatsoever)
def EuclidGeometry.Lines_Intersect2
  (l1 l2 : geom.Line) (p : geom.Point) :
  Prop
  := geom.lies_on p l1 ∧ geom.lies_on p l2


-- lines, when they intersect, they do so at a unique point
theorem EuclidGeometry.Lines_Intersect_Point_Unique
  (l1 l2 : geom.Line) (h : Lines_Intersect geom l1 l2) (A B : geom.Point) :
  Lines_Intersect2 geom l1 l2 A → 
  Lines_Intersect2 geom l1 l2 B →
  A = B
  := by
    intro h1 h2
    by_contra hab
    simp [Lines_Intersect2] at h1
    let ⟨h1l, h1r⟩ := h1
    simp [Lines_Intersect2] at h2
    let ⟨h2l, h2r⟩ := h2
    have lem1 : l1 = l2 := by
      apply geom.line_unique A B hab
      simp [h1l, h1r, h2l, h2r]
    simp [Lines_Intersect, IsParallel] at h
    rw [not_or] at h
    let ⟨hk, _⟩ := h
    contradiction

    






/-
variable (Point_from_lines_intersection : 
  (l1 : geom.Line) →  (l2 : geom.Line) →  (geom.Lines_Intersect l1 l2) →  geom.Point)

#check Point_from_lines_intersection

-- property of Point_from_lines_intersection
def 
-/



-- intersection of a line and a segment 
def EuclidGeometry.Line_Intersect_Segment
  (seg : Segment geom) (l : geom.Line) : Prop := 
  ∃ p : geom.Point, geom.lies_on p l ∧ geom.lies_on_segment p seg

-- intersection of a line and a segment at point p
def EuclidGeometry.Line_Intersect_Segment2
  (seg : Segment geom) (l : geom.Line) (p : geom.Point): Prop := 
  geom.lies_on p l ∧ geom.lies_on_segment p seg




--variable (post2: Post2 geom)


-- postulate 3
structure Circle (geom : EuclidGeometry) where
  centre : geom.Point
  radius : ℝ


-- points on circle
def EuclidGeometry.On_Circle (P : geom.Point) (circ : Circle geom) : Prop
  := geom.distance P circ.centre = circ.radius



-- postulate 4
structure Angle (geom : EuclidGeometry) where
  p1 : geom.Point
  Pivot : geom.Point
  p2 : geom.Point



variable (reflexAngle : Angle geom → Angle geom)

-- measure of angle
variable (mAngle : Angle geom → ℝ)


-- statement that a point is inside an angle
def EuclidGeometry.IntPointAngle (a : geom.Point) (A : Angle geom) : Prop :=
  let A1 : Angle geom := Angle.mk a A.Pivot A.p1
  have A2 : Angle geom := Angle.mk a A.Pivot A.p2
  (mAngle (A1) < mAngle  A) ∧ (mAngle (A2) < mAngle A) -- strict inequality because of 120  


-- we need to write that intpointangle for angles AOB and BOA are the same


-- properties of mAngle
def EuclidGeometry.mAngle_non_neg (a b c : geom.Point) : Prop := 
  mAngle (Angle.mk a b c) ≥ 0 
def EuclidGeometry.ZeroAngle (a b c : geom.Point) (_ : geom.in_between a c b): Prop := 
  mAngle (Angle.mk a b c) = 0
def EuclidGeometry.mAngle_postive (a b c : geom.Point) : Prop :=
  ¬ geom.in_between a c b → 
  ¬ geom.in_between c a b → 
  mAngle (Angle.mk a b c) > 0

def EuclidGeometry.mReflexAngle (A : Angle geom) : Prop := 
  mAngle (reflexAngle A) = 360 - mAngle A



-- Angle A as Sum of its constituents
def EuclidGeometry.mAngleAdd (a : geom.Point) (A : Angle geom) 
  (_ : EuclidGeometry.IntPointAngle geom mAngle a A) :
  have A1 : Angle geom := Angle.mk a A.Pivot A.p1
  have A2 : Angle geom := Angle.mk a A.Pivot A.p2
  mAngle A = mAngle A1 + mAngle A2
  := sorry


-- Postulate 4 says all right angles are equal.
-- We are assigning it a value of 90
def EuclidGeometry.isRightAngle (A : Angle geom): Prop := mAngle A = 90
-- straight line is two right angles

def EuclidGeometry.StraightAngle (a b c : geom.Point) (_ : geom.in_between a b c) :
  mAngle (Angle.mk a b c) = 180 := sorry

--variable (StraightAngle) --(a b c : geom.Point) (_ : geom.in_between a b c) :
  --mAngle (Angle.mk a b c) = 180



-- Postulate 5

-- defining when two points are on opposite sides of a line
def EuclidGeometry.OppSidedPoints (p1 p2 : geom.Point) (l : geom.Line) : Prop :=
  geom.Line_Intersect_Segment (Segment.mk p1 p2) l


-- defining same sided points
def EuclidGeometry.SameSidedPoints (p1 p2 : geom.Point) (l : geom.Line) : Prop :=
  ¬ geom.OppSidedPoints p1 p2 l


-- Statement of Postulate 5: 
-- Let line segment AB and CD be intersected by 
-- line l at points p1 and p2 respectively.
-- Let A and C be same-sided wrt l.
-- Let mAngle(A p1 p2) + mAngle(C p2 p1) < 180.
-- Then there exists a point p such that
-- line from AB and CD intersect at p
-- and p is same-sided as A wrt to line l.

def EuclidGeometry.Post5 (A B C D p1 p2 : geom.Point) (l : geom.Line)
  (hab : ¬ A = B) (hcd : ¬ C = D) : Prop :=
  geom.Line_Intersect_Segment2 (Segment.mk A B) l p1
  →
  geom.Line_Intersect_Segment2 (Segment.mk C D) l p2
  → 
  geom.SameSidedPoints A C l
  → 
  mAngle (Angle.mk A p1 p2) + mAngle (Angle.mk C p2 p1) < 180
  → 
  ∃ p : geom.Point, 
  geom.Lines_Intersect2 
  (geom.Line_of_two_points A B hab) (geom.Line_of_two_points C D hcd) p
  ∧ 
  geom.SameSidedPoints p A l





-- vertically opposite angles are equal

-- equality of measure of "symmetric" angles
def EuclidGeometry.SymmAngles (a o b : geom.Point): 
  mAngle (Angle.mk a o b) = mAngle (Angle.mk b o a)
  := sorry


theorem VOAequal (a b c d o : geom.Point) 
(h1 : ¬a = b)
(h2 : ¬c = d)
(h3 : geom.in_between a o b ∧ geom.in_between c o d)
(h4 : ¬geom.IsParallel 
  (geom.Line_of_two_points a b h1) 
  (geom.Line_of_two_points c d h2)) 
(h5: geom.IntPointAngle mAngle c (Angle.mk a o b)) 
(h6: geom.IntPointAngle mAngle a (Angle.mk c o d)):
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
  have lem1 : mAngle (AOB) = 180 := geom.StraightAngle mAngle a o b (And.left h3)
  have lem2 : mAngle (COD) = 180 := geom.StraightAngle mAngle c o d (And.right h3)
  have lem3 : mAngle (AOB) = mAngle (COA) + mAngle (COB) := 
    geom.mAngleAdd mAngle c AOB h5
  have lem4 : mAngle (COD) = mAngle (AOC) + mAngle (AOD) := 
    geom.mAngleAdd mAngle a COD h6
  have lem5 : mAngle COA = mAngle AOC := by 
    simp [geom.SymmAngles]
  have lem6 : mAngle (COA) + mAngle (COB) = mAngle (AOC) + mAngle (AOD) := by
    rw [<-lem3, <-lem4, lem1, lem2]
  rw [lem5] at lem6
  simp [add_left_cancel] at lem6
  assumption
  






--def reflexAngle (a : Angle geom) : Angle geom 
  --:= (Angle geom).mk 



structure Postulates (geom: EuclidGeometry) where
  post2 : ∀ s : Segment geom, ∃ l: geom.Line, geom.segment_in_line s l

--we would need to call these postulates to prove theorems within EuclidGeometry. Some other smaller definitions
-- and theorems require these postulates as "inputs".
