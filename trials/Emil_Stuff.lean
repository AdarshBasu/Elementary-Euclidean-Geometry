import Lake
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector

import Mathlib.Algebra.Group.Defs


#eval 1


set_option autoImplicit false

-- Geometry from Chapter 2 of Emil Artin

structure EmilGeometry /- (Point Line : Type) -/ where
  Point : Type
  Line : Type
  
  /-- The point lies on the given line.-/
  lies_on : Point → Line → Prop

  is_parallel (l1 l2 : Line) : Prop := 
  (l1 = l2) ∨ (∀ a : Point, lies_on a l1 ↔ ¬ lies_on a l2)


  axiom1 (p1 p2 : Point) (h: ¬ p1 = p2) : 
    ∃! l : Line, ((lies_on p1 l) ∧ (lies_on p2 l))

  line_two_points (p1 p2 : Point) (h : ¬ p1 = p2) : Line -- deletable

  

  
  playfair (p: Point) (l: Line) : 
    ∃! m : Line, (lies_on p m) ∧ (is_parallel l m)


  line_parallel_line (p : Point) (l : Line) : Line -- this line is parallel to l and passing through p
  -- deletable

  -- could not extract (a ≠ b) for axiom3. so we have written this auxiliary theorem
  -- to say that there exists three distinct points.
  aux3 : ∃ (a b c : Point), (¬ a = b) ∧ (¬ b = c) ∧ (¬ a = c)

  axiom3 (a b : Point) (hab : ¬ a = b) :
    ∃ (c : Point), ¬ lies_on c (line_two_points a b hab)
  

/- TODO:
  There is no property that relates (line_two_points a b) with the points a, b 
  themselves.
  Need to say that (line_two_points a b) contains a and also contains b.
  So, axiom3 makes no sense currently.
-/

variable {geom : EmilGeometry}


#check Exists
#check Vector
#check Subtype



-- infix:64 "||" => EmilGeometry.is_parallel
-- infix:64 "+!" => EmilGeometry.line_two_points



-- def someprop (f : geom.Point → geom.Point) : Prop := 
--   ∀ p1 p2 : geom.Point, geom.is_parallel (geom.line_two_points p1 p2) (geom.line_two_points (f p1 ) (f p2)) 


-- Defining Dilatation
-- def EmilGeometry.Dilatation : Subtype := 
--   {f : geom.Point → geom.Point // 
--     ∀ p1 p2 : geom.Point, (h12 : ¬ p1 = p2) 
--     → geom.is_parallel (geom.line_two_points p1 p2 (h12 : ¬ p1 = p2)) (l : geom.Line)}


-- def funct : (a b : Nat) → (hab : ¬ a = b) → ¬ a = b := by



structure Dilatation where
  func : geom.Point → geom.Point
  prop : (a b : geom.Point) → (hab : ¬ a = b) → 
    geom.lies_on (func b) (geom.line_parallel_line (func a) (geom.line_two_points a b hab))





--#check Subtype.mk ((geom.Line) → (geom.Line) → Prop) 
 -- ((l1 = l2) ∨ (∀ a : geom.Point, geom.lies_on a l1 → ¬ geom.lies_on a l2))


---def EmilGeometry.is_parallel2 (l1 l2 : geom.Line) : Prop :=
 --- (l1 = l2) ∨ (∀ a : geom.Point, geom.lies_on a l1 → ¬ geom.lies_on a l2)


