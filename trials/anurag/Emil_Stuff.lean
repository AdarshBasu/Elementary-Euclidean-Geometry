import Lake
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector

import Mathlib.Algebra.Group.Defs


#eval 1
#check Group

set_option autoImplicit false

-- Geometry from Chapter 2 of Emil Artin

/-TODo:
 - for commutative group, use AddCommGroup-/


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

open EmilGeometry

def EmilGeometry.lineOf {geom : EmilGeometry}(p q: geom.Point)(h : ¬p = q) :=
  geom.line_of p q h

#check geom.axiom3
#check Exists
#check Vector
#check Subtype


-- infix:64 "||" => EmilGeometry.is_parallel
-- infix:64 "|!" => EmilGeometry.line_parallel_line
-- infix:100 "+!" => EmilGeometry.line_two_points
-- try "notation" and "macro"

macro  a:term "+!" b:term ":::" c:term : term => do
  `(EmilGeometry.lineOf $a:term $b:term $c:term)






-- def someprop (f : geom.Point → geom.Point) : Prop := 
--   ∀ p1 p2 : geom.Point, geom.is_parallel (geom.line_two_points p1 p2) (geom.line_two_points (f p1 ) (f p2)) 


--Defining Dilatation as a Subtype

structure EmilGeometry.Dilatation := 
  func : geom.Point → geom.Point
  prop : ∀ p1 p2 : geom.Point, (h12 : ¬ p1 = p2) → 
    (geom.lies_on (func p2) (geom.para_line_playfair (func p2) (p1 +! p2 ::: h12)))

#print EmilGeometry.Dilatation

@[ext] theorem EmilGeometry.Dilatation.ext (d1 d2 : geom.Dilatation) : d1.func = d2.func → d1 = d2 := by
  intro hyp
  cases d1
  cases d2
  simp
  subst hyp -- substitute
  rfl

-- theorem EmilGeometry.closure_dil : (d1 d2 : geom.Dilatation) → ∃ d : geom.Dilatation, d.val = (fun p => d1.val (d2.val p)) := by
--   intro d1 d2
--   let f := fun p => d1.val (d2.val p)
--   have lem1 : ∀ p1 p2 : geom.Point, (h12 : ¬ p1 = p2) → 
--     (geom.lies_on (f p2) (geom.para_line_playfair (f p2) (geom.line_of p1 p2 h12))) := by
--     simp [EmilGeometry.axiom1, EmilGeometry.playfair]
--   let d : geom.Dilatation := ⟨f, lem1⟩
--   apply Exists.intro d (by simp) -- not necessary



abbrev EmilGeometry.comp_dil (d1 d2 : geom.Dilatation) : geom.Dilatation :=
  ⟨fun p => d1.func (d2.func p), (by simp [axiom1,playfair])⟩

--infix:64 "⋆" => EmilGeometry.comp_dil

#check EmilGeometry.Dilatation

instance : Group (geom.Dilatation) where
  mul := geom.comp_dil
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry
  mul_assoc := by
    intro a b c
    ext x
    show (comp_dil (comp_dil a b) c).func x =  Dilatation.func (comp_dil a (comp_dil b c)) x
    simp [comp_dil]







-- def funct : (a b : Nat) → (hab : ¬ a = b) → ¬ a = b := by



-- structure Dilatation where
--   func : geom.Point → geom.Point
--   prop : (a b : geom.Point) → (hab : ¬ a = b) → 
--     geom.lies_on (func b) (geom.line_parallel_line (func a) (geom.line_two_points a b hab))




