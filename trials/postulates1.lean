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
  


structure EuclidGeometry extends IncidenceGeometry where
  --Segment : Type := Point × Point
  --contain_end_points (seg : Segment) : --says the end points of the segment lies on the resulting line
  --  lies_on (seg.1) (line_from_seg seg) ∧ lies_on (seg.2) (line_from_seg seg)
  

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
  -- end of Postulate 1
  
  -- Postulate 2
  -- A line segment can be extended to get a line
  
  points_betw_on_line (a b c : Point) (h : in_between a b c) (k : ¬ a = c):
  --says that a point "b" that is between "a", "c" will be on the line joining them
    lies_on b (Line_of_two_points a c k)
  --line_from_seg (seg : Segment) : Line --says a you get a line from a segment

abbrev Seg (geom: IncidenceGeometry) := geom.Point × geom.Point

#check Exists

#check Prod 
 
structure Segment (geom : IncidenceGeometry) where
  p1 : geom.Point
  p2 : geom.Point

instance : Coe EuclidGeometry IncidenceGeometry where
  coe geom := { Point := geom.Point, Line := geom.Line, lies_on := geom.lies_on, in_between := geom.in_between, between_refl_left := geom.between_refl_left, between_refl_right := geom.between_refl_right }

#check Coe.coe

def EuclidGeometry.length (geom : EuclidGeometry) (s : Segment geom) : ℝ :=
  geom.distance s.p1 s.p2



-- def EuclidGeometry.point_on_segment (geom : EuclidGeometry) (s : Segment geom) (p : geom.Point) : Prop :=
--   geom.in_between s.p1 p s.p2


def EuclidGeometry.segment_in_line (geom: EuclidGeometry) 
  (s: Segment geom)(l: geom.Line) : Prop :=
  ∀ p: geom.Point, geom.in_between s.p1 p s.p2 → geom.lies_on p l

def Post2 (geom : EuclidGeometry) : Prop := 
  ∀ s : Segment geom, ∃ l: geom.Line, geom.segment_in_line s l


variable (geom: EuclidGeometry)

variable (post2: Post2 geom)

structure Postulates (geom: EuclidGeometry) where
  post2 : ∀ s : Segment geom, ∃ l: geom.Line, geom.segment_in_line s l

--we would need to call these postulates to prove theorems within EuclidGeometry. Some other smaller definitions
-- and theorems require these postulates as "inputs".
