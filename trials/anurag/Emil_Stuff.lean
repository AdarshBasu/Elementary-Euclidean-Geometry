import Lake
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector

import Mathlib.Algebra.Group.Defs


#eval 1
#check Group

set_option autoImplicit false

-- Geometry from Chapter 2 of Emil Artin

structure EmilGeometry where
  Point : Type
  Line : Type
  
  /- The point lies on the given line.-/
  lies_on : Point → Line → Prop

  is_parallel (l1 l2 : Line) : Prop := 
  (l1 = l2) ∨ (∀ a : Point, lies_on a l1 ↔ ¬ lies_on a l2)


  line_of (p1 p2 : Point) (h : ¬ p1 = p2) : Line
  
  -- include "line_of_property"

  axiom1 (p1 p2 : Point) (h: ¬ p1 = p2) :
    let l := line_of p1 p2 h
    (lies_on p1 l) ∧ (lies_on p2 l) ∧ 
    (∀ l' : Line, ((lies_on p1 l') ∧ (lies_on p2 l')) → l = l')


  para_line_playfair (p : Point) (l : Line) : Line
  
  playfair (p: Point) (l: Line) :
    let m := para_line_playfair p l
    (lies_on p m) ∧ (is_parallel l m) ∧ 
    (∀ m' : Line, ((lies_on p m') ∧ (is_parallel l m')) → m = m')


   -- this line is parallel to l and passing through p
  -- deletable

  -- could not extract (a ≠ b) for axiom3. so we have written this auxiliary theorem
  -- to say that there exists three distinct points.
  --aux3 : ∃ (a b c : Point), (¬ a = b) ∧ (¬ b = c) ∧ (¬ a = c)

  axiom3 : ∃ (a b c : Point) (h : (¬ a = b) ∧ (¬ b = c) ∧ (¬ a = c)), 
    ¬ lies_on c (line_of a b (h.left)) 
  -- wanted to extract the line from "axiom1" and not using this hack function "line_of"
  

/- TODO:
  There is no property that relates (line_two_points a b) with the points a, b 
  themselves.
  Need to say that (line_two_points a b) contains a and also contains b.
  So, axiom3 makes no sense currently.
-/

variable {geom : EmilGeometry}



#check geom.axiom3
#check Exists
#check Vector
#check Subtype


-- infix:64 "||" => EmilGeometry.is_parallel
-- infix:64 "|!" => EmilGeometry.line_parallel_line
-- infix:100 "+!" => EmilGeometry.line_two_points
-- try "notation" and "macro"



-- def someprop (f : geom.Point → geom.Point) : Prop := 
--   ∀ p1 p2 : geom.Point, geom.is_parallel (geom.line_two_points p1 p2) (geom.line_two_points (f p1 ) (f p2)) 


--Defining Dilatation
def EmilGeometry.Dilatation := 
  {f : geom.Point → geom.Point // 
    ∀ p1 p2 : geom.Point, (h12 : ¬ p1 = p2) → 
    (geom.lies_on (f p2) (geom.para_line_playfair (f p2) (geom.line_of p1 p2 h12)))
    }

#print EmilGeometry.Dilatation



-- theorem EmilGeometry.closure_dil : (d1 d2 : geom.Dilatation) → ∃ d : geom.Dilatation, d.val = (fun p => d1.val (d2.val p)) := by
--   intro d1 d2
--   let f := fun p => d1.val (d2.val p)
--   have lem1 : ∀ p1 p2 : geom.Point, (h12 : ¬ p1 = p2) → 
--     (geom.lies_on (f p2) (geom.para_line_playfair (f p2) (geom.line_of p1 p2 h12))) := by
--     simp [EmilGeometry.axiom1, EmilGeometry.playfair]
--   let d : geom.Dilatation := ⟨f, lem1⟩
--   apply Exists.intro d (by simp) -- not necessary



def EmilGeometry.comp_dil (d1 d2 : geom.Dilatation) : geom.Dilatation :=
  ⟨fun p => d1.val (d2.val p), (by simp [axiom1,playfair])⟩

--infix:64 "⋆" => EmilGeometry.comp_dil

#check EmilGeometry.Dilatation

instance : Group (geom.Dilatation) where
  mul := fun d1 d2 => geom.comp_dil d1 d2
  mul_assoc := by
    simp [EmilGeometry]
    





-- def funct : (a b : Nat) → (hab : ¬ a = b) → ¬ a = b := by



-- structure Dilatation where
--   func : geom.Point → geom.Point
--   prop : (a b : geom.Point) → (hab : ¬ a = b) → 
--     geom.lies_on (func b) (geom.line_parallel_line (func a) (geom.line_two_points a b hab))



