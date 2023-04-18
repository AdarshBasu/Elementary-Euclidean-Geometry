import Lake
import Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector
import Mathlib.Algebra.Group.Defs


set_option autoImplicit false

/-
In analytic geometry, points on the plane can be described using a pair of points (x, y). It allows us to change any elementary geometric problem into an algebraic one. What about the converse?
Given plane geometry, can we obtain the likes of analytic geometry?
Desargues' theorem gives the answer in the affirmative.
We attempt to prove Desargues' theorem from the basic axioms of incidence geometry. We follow the path laid down in Chapter 2 of Emil Artin's Geometric Algebra.
We start out by defining incidence axioms and properties.
Then we introduce parallel lines. Finally, we introduce dilatations.
We have currently proved (partially) that non-trivial Dilatations form a group.

There is still a long way to Desargues' theorem.

Main Goal: Desargues' theorem

Current Status: Non-trivial dilatations form a group (partial proof).

Defn of Dilatation:
A map `d : Point → Point` is called a dilatation if it has the following property:
Let `p q : Point` be distinct,
`p' q' : Point` be their images.
If `l' : Line` is parallel to `line_of p q` which passes through `p'`,
then
`l'` passes through `q'` as well.
-/


structure EmilGeometry where
  Point : Type
  Line : Type
  
  /-- `lies_on p l` is a prop that `p` is a point on Line `l`.-/
  lies_on : Point → Line → Prop


variable {geom : EmilGeometry}


/--`is_parallel l1 l2` is a prop that Lines `l1` is parallel to `l2`-/
def EmilGeometry.is_parallel (l1 l2 : geom.Line) : Prop := 
  (l1 = l2) ∨ (∀ a : geom.Point, geom.lies_on a l1 → ¬ geom.lies_on a l2)



structure EmilGeomAxioms extends EmilGeometry where
  /--`line_of p1 p2 h` is a Line. axiom1 ensures that this is the only line passing through `p1` and `p2`-/
  line_of (p1 p2 : Point) (h : ¬ p1 = p2) : Line

  -- some basic properties of "lies_on"
  /--Endpoints `p q : Point` of a line segment `line_of p q` lie on the unique line passing through them-/
  lies_on_endpoints (p q : Point) (hpq : ¬ p = q) : lies_on p (line_of p q hpq) ∧ lies_on q (line_of p q hpq)

  /--states property of the `line_of p1 p2 h` that ensures that it is the unique Line passing through the given points-/
  axiom1 (p1 p2 : Point) (h: ¬ p1 = p2) :
    let l := line_of p1 p2 h
    ((lies_on p1 l) ∧ (lies_on p2 l)) ∧ 
    (∀ l' : Line, ((lies_on p1 l') ∧ (lies_on p2 l')) → l = l')

  /--`para_line_playfair p l` is a Line. axiom2 ensures that this is the only line parallel to `l` and passing through `p`-/
  para_line_playfair (p : Point) (l : Line) : Line
  /--states property of the `para_line_playfair p l` that ensures that it is the unique Line parallel to `l` and passing through `p`-/
  axiom2 (p: Point) (l: Line) :
    let m := para_line_playfair p l
    ((lies_on p m) ∧ (EmilGeometry.is_parallel l m)) ∧ 
    (∀ m' : Line, ((lies_on p m') ∧ (EmilGeometry.is_parallel l m')) → m = m')

  /--`axiom3` states that the geometry contains three non-colinear points.-/
  axiom3 : ∃ (a b c : Point) (h : (¬ a = b) ∧ (¬ b = c) ∧ (¬ a = c)), 
    ¬ lies_on c (line_of a b (h.left))
  

  /--`Intersection` takes two non-parallel lines `l m : Line` and returns `Point`.-/
  Intersection (l m : Line) (h : ¬ EmilGeometry.is_parallel l m) : Point
  /--`Intersection` property that the intersection point of two non-parallel lines `l m : Line` lies on both these lines.-/
  prop_exist (l m : Line) (h : ¬ EmilGeometry.is_parallel l m) : (lies_on (Intersection l m h) l ∧ lies_on (Intersection l m h) m) ∧ (∀ p : Point, lies_on p l ∧ lies_on p m → p = (Intersection l m h))

  /--`Axiom3` was the statement that there exists three non-collinear points. `point_ax3`: returns a point on input two distinct points `a b : Point`. Its property is stated in `point_ax3_prop`.-/
  point_ax3 (a b : Point) (hab : ¬ a = b) : Point
  /--Non-collinearity property of the point from `point_ax3`.-/
  point_ax3_prop (a b : Point) (hab : ¬ a = b) :
    let c := point_ax3 a b hab
    ¬ lies_on c (line_of a b hab)



instance : Coe EmilGeomAxioms EmilGeometry where
  coe geom := {Point := geom.Point, Line := geom.Line, lies_on := geom.lies_on}

variable {ega : EmilGeomAxioms}
open EmilGeomAxioms


/--`line_of_line_eq p q hpq l` states that if both distinct `p q : Point` lie on `l : Line`, then `line_of p q = l`. -/
theorem EmilGeomAxioms.line_of_line_eq (p q : ega.Point) (hpq : ¬ p = q) (l : ega.Line) : (ega.lies_on p l ∧ ega.lies_on q l) → ega.line_of p q hpq = l := by
  intro hyp
  let h := (ega.axiom1 p q hpq).right
  apply h
  assumption

/--`point_not_on_line a b hab` takes `a b : Point` and `hab : ¬ a = b` to give a point `c` such that `c` does not line on `line_of a b`.-/
theorem EmilGeomAxioms.point_not_on_line (a b : ega.Point) (hab : ¬ a = b) : ∃ c : ega.Point, ¬ ega.lies_on c (ega.line_of a b hab) := by

  by_contra hc
  simp [not_exists] at hc

  let ⟨ p, q, r, hpqr, k⟩ := ega.axiom3
  have lem1 : ega.lies_on r (ega.line_of a b hab) ∧ ega.lies_on p (ega.line_of a b hab) ∧ ega.lies_on q (ega.line_of a b hab) := by simp [hc]

  have lem2 : ega.line_of p q hpqr.left = ega.line_of a b hab := by
    apply ega.line_of_line_eq p q hpqr.left (ega.line_of a b hab)
    simp [lem1]
  
  have lem3 : ega.lies_on r (line_of ega p q hpqr.left) := by
    simp [lem2]
    simp [lem1]
  contradiction



/--`not_parallel_common_point` states that if two lines are not parallel, then they have a common point-/
theorem EmilGeomAxioms.not_parallel_common_point (l m : ega.Line) (h : ¬ ega.is_parallel l m) : ∃ p : ega.Point, ega.lies_on p l ∧ ega.lies_on p m := by
  unfold EmilGeometry.is_parallel at h
  simp [not_or] at h
  let ⟨_,h2⟩ := h
  assumption  
  


/--`not_parallel_unique_point` states that if two lines are not parallel, then they can not intersect at more than one point. Syntax: `not_parallel_unique_point l m h` where `l m : Line` and `h : ¬ is_parallel l m`.-/
theorem EmilGeomAxioms.not_parallel_unique_point (l m : ega.Line) (h : ¬ ega.is_parallel l m) : (∀ p q : ega.Point, ega.lies_on p l ∧ ega.lies_on p m ∧ ega.lies_on q l ∧ ega.lies_on q m → p = q) := by
  unfold EmilGeometry.is_parallel at h
  simp [not_or] at h
  let ⟨h1,_⟩ := h
  intro q r hyp
  let ⟨hql,hqm,hrl,hrm⟩ := hyp
  by_contra hqr
  have lem1 : ega.line_of q r hqr = l := by
    apply ega.line_of_line_eq q r hqr l
    simp [hql, hrl]
  have lem2 : ega.line_of q r hqr = m := by
    apply ega.line_of_line_eq q r hqr m
    simp [hqm, hrm]
  have lem3 : l = m := by
    simp [<-lem1, lem2]
  contradiction


/--A line which satisfies the conditions of axiom2 is equal to `para_line_plarfair`-/
theorem EmilGeomAxioms.para_line_playfair_def (p : ega.Point) (l m : ega.Line) (h : ega.lies_on p m) (h' : ega.is_parallel l m) : ega.para_line_playfair p l = m := by
  have lem1 : (ega.lies_on p m) ∧ (ega.is_parallel l m) := ⟨h, h'⟩
  let m' := ega.para_line_playfair p l
  have lem2 : m' = m := by
    apply (ega.axiom2 p l).right
    assumption
  simp [lem2]



/--`is_parallel` is a reflexive relation on Line-/
theorem EmilGeomAxioms.para_refl : ∀ l : ega.Line, ega.is_parallel l l := by
  intro l
  apply Or.inl
  rfl

/--`para_line_playfair` is the same as the line if the point lies on the line-/
theorem EmilGeomAxioms.para_line_playfair_is_same (p : ega.Point) (l : ega.Line) (h : ega.lies_on p l) : ega.para_line_playfair p l = l := by
  have lem1 : (ega.lies_on p l) ∧ (ega.is_parallel l l) := ⟨h, ega.para_refl l⟩
  let m := ega.para_line_playfair p l
  --have lem2 : (ega.lies_on p m) ∧ (ega.is_parallel l m) := (ega.axiom2 p l).left
  have lem3 : m = l := by
    apply (ega.axiom2 p l).right
    assumption
  simp [lem3]


/--`is_parallel` is a symmetric relation on Line-/
theorem EmilGeomAxioms.para_symm : ∀ l m : ega.Line, ega.is_parallel l m → ega.is_parallel m l := by
  intro l m h
  apply Or.elim h
  case left =>
    intro h'
    rw [h']
    simp [para_refl]
  case right =>
    intro h'
    unfold EmilGeometry.is_parallel
    apply Or.inr
    intro a
    have lem1 := show ega.lies_on a l → ¬ ega.lies_on a m from h' a
    simp [imp_not_comm]
    assumption



/--`is_parallel` is a transtive relation on Line-/
theorem EmilGeomAxioms.para_trans : ∀ l m n : ega.Line, ega.is_parallel l m → ega.is_parallel m n → ega.is_parallel l n := by
  intro l m n h1 h2
  by_contra h3
  let ⟨p, h4, h5⟩ := ega.not_parallel_common_point l n h3
  have h6 : ega.para_line_playfair p m = l := ega.para_line_playfair_def p m l h4 (ega.para_symm l m h1)
  have h7 : ega.para_line_playfair p m = n := ega.para_line_playfair_def p m n h5 h2
  have h8 : l = n := by
    rw [h6] at h7
    assumption
  rw [h8] at h3
  have h9 : ega.is_parallel n n := (ega.para_refl n)
  contradiction
    

/-- If point `q` distinct from `p` lies on `para_line_playfair p l` then `line_of p q` is parallel to it. -/
theorem EmilGeomAxioms.lies_on_playfair (p q : ega.Point) (h : p ≠ q) (l : ega.Line) : ega.lies_on q (ega.para_line_playfair p l) → ega.is_parallel (ega.line_of p q h) l := by
  intro h'
  let m := ega.para_line_playfair p l
  have lem1 : ega.line_of p q h = m := by
    apply (ega.axiom1 p q h).right
    apply And.intro
    case a.left =>
      simp [axiom2]
    case a.right =>
      assumption
  rw [lem1]
  have lem2 : EmilGeometry.is_parallel l m := by
    apply (ega.axiom2 p l).left.right
  apply ega.para_symm
  assumption
  

-- defining a macro for `line_of`. We don't use it as much.
macro  a:term "+!" b:term "-!" c:term : term => do
  `(ega.line_of $a:term $b:term $c:term)



/--`Dilatation` is a function from Point to Point which maps points on any given line to a points on a line which is parallel to it-/

structure EmilGeomAxioms.Dilatation := 
  func : ega.Point → ega.Point
  prop : ∀ p1 p2 : ega.Point, (h12 : ¬ p1 = p2) → 
    (ega.lies_on (func p2) (ega.para_line_playfair (func p1) (p1 +! p2 -! h12)))

/--Extensionality theorem for Dilatations-/
@[ext] theorem EmilGeomAxioms.Dilatation.ext (d1 d2 : ega.Dilatation) : d1.func = d2.func → d1 = d2 := by
  intro hyp
  cases d1
  cases d2
  simp
  subst hyp-- substitute
  rfl


/--`r: point` not on `line_of p q` is not equal to `p q`-/
theorem EmilGeomAxioms.point_not_on_line_not_eq (p q r : ega.Point) (hpq : ¬ p = q) : ¬ ega.lies_on r (ega.line_of p q hpq) → ¬p = r ∧ ¬q = r := by
  intro hyp
  apply And.intro
  case left => 
    by_contra h 
    rw[<-h] at hyp
    simp [ega.lies_on_endpoints] at hyp
  case right => 
    by_contra h
    rw[<-h] at hyp
    simp [ega.lies_on_endpoints] at hyp


/--`r : Point` not on `line_of p q`. then `line_of p r` not parallel to `line_of q r`. -/
theorem EmilGeomAxioms.point_not_on_line_not_parallel (p q r : ega.Point) (hpq : ¬ p = q) : (hyp : ¬ ega.lies_on r (ega.line_of p q hpq)) → ¬ ega.is_parallel (ega.line_of p r (ega.point_not_on_line_not_eq p q r hpq hyp).left) (ega.line_of q r (ega.point_not_on_line_not_eq p q r hpq hyp).right) := by
  intro hyp1
  by_contra h 
  apply Or.elim h
  case left =>
    intro hyp11
    have lem_lies1 : ega.lies_on q (ega.line_of p r (ega.point_not_on_line_not_eq p q r hpq hyp1).left) := by
      rw[hyp11]
      simp [ega.lies_on_endpoints]
        
    have lem_eq1 : ega.line_of p q (hpq) = (ega.line_of p r (ega.point_not_on_line_not_eq p q r hpq hyp1).left) := by
      apply ega.line_of_line_eq
      simp [ega.lies_on_endpoints, lem_lies1]
    rw[lem_eq1] at hyp1
    simp[ega.lies_on_endpoints] at hyp1
  case right =>
    intro hyp12
    have lem11 : ega.lies_on r (ega.line_of p r (ega.point_not_on_line_not_eq p q r hpq hyp1).left) ∧ ega.lies_on r (ega.line_of q r (ega.point_not_on_line_not_eq p q r hpq hyp1).right) := by simp[ega.lies_on_endpoints]
    have lem12 : ¬ ega.lies_on r (ega.line_of q r (ega.point_not_on_line_not_eq p q r hpq hyp1).right) := by
      simp[hyp12, lem11]
    have lem13 : ega.lies_on r (ega.line_of q r (ega.point_not_on_line_not_eq p q r hpq hyp1).right) := by apply lem11.right
    contradiction
  
    
/--If `d1 d2 : Dilatation` map `a b : Point` to the same points, i.e., `d1(a) = d2(a)` and `d1(b) = d2(b)`, then it will map `r : Point` which is not on `line_of a b` to the same point, i.e., `d1(r) = d2(r)`. This theorem was needed for theorems `Diltn_unique`, `Diltn_oneone_onto`-/
theorem EmilGeomAxioms.Diltn_aux_thm (a b r : ega.Point) (hab : ¬ a = b) (d1 d2 : ega.Dilatation) (hypab : d1.func a = d2.func a ∧ d1.func b = d2.func b) (h : ¬ (ega.lies_on r (ega.line_of a b hab))) : d1.func r = d2.func r := by
    let x1 := d1.func r
    let x2 := d2.func r

    --lem0 is proved
    have lem0 : (¬ a = r) ∧ (¬ b = r) := by
      apply And.intro
      case left =>
        by_contra hpx
        have lem1 : (ega.lies_on r (ega.line_of a b hab)) := by
          rw [<-hpx]
          simp[(ega.lies_on_endpoints a b hab).left]
        contradiction
      case right =>
        by_contra hqx
        have lem1 : (ega.lies_on r (ega.line_of a b hab)) := by
          rw [<-hqx]
          simp[(ega.lies_on_endpoints a b hab).right]
        contradiction
    -- end of lem0 proof

    --lem1 is not proved yet
    have lem1 : ¬ ega.is_parallel (ega.line_of a r (lem0.left)) (ega.line_of b r (lem0.right)) := by

      simp [ega.point_not_on_line_not_parallel, hab, h]
    --end of lem1 proof

    --lem2 (PROVED) : line passing thru d1(p) parallel to (p+x) also contains d1(x)
    have lem2p : ega.lies_on x1 (ega.para_line_playfair (d1.func a) (ega.line_of a r (lem0.left))) := by
      show EmilGeometry.lies_on ega.toEmilGeometry (d1.func r) (ega.para_line_playfair (d1.func a) (line_of ega a r (_ : ¬a = r)))
      apply d1.prop a r (lem0.left)
    -- end of lem2 proof

    --lem3 (PROVED) : line passing thru d1(p) parallel to (p+x)
              --  and line passing thru d2(p) parallel to (p+x)
              --      are the same line as d1(p) = d2(p)
    have lem3p : ega.para_line_playfair (d1.func a) (ega.line_of a r (lem0.left)) = ega.para_line_playfair (d2.func a) (ega.line_of a r (lem0.left)) := by rw[hypab.left]
    -- end of lem3 proof

    -- lem4 : same as lem2 but for d2(x)
    have lem4p : ega.lies_on x2 (ega.para_line_playfair (d2.func a) (ega.line_of a r (lem0.left))) := by
      show EmilGeometry.lies_on ega.toEmilGeometry (d2.func r) (ega.para_line_playfair (d2.func a) (line_of ega a r (_ : ¬a = r)))
      apply d2.prop a r (lem0.left)
    -- end of lem4 proof

    -- lem5 : x1, x2 both lie on the same line parallel to (p+x)
    have lem5p : ega.lies_on x2 (ega.para_line_playfair (d2.func a) (ega.line_of a r (lem0.left))) 
    ∧ ega.lies_on x1 (ega.para_line_playfair (d2.func a) (ega.line_of a r (lem0.left))) := by
      apply And.intro
      case left => apply lem4p
      case right => 
        simp
        rw[<-lem3p]
        apply lem2p
    -- end of lem5 proof

    -- We shall now show the same thing for the line parallel to (q + x) 
    -- and passing thru d1(q)

    --lem2 (PROVED) : line passing thru d1(p) parallel to (p+x) also contains d1(x)
    have lem2q : ega.lies_on x1 (ega.para_line_playfair (d1.func b) (ega.line_of b r (lem0.right))) := by
      show EmilGeometry.lies_on ega.toEmilGeometry (d1.func r) (ega.para_line_playfair (d1.func b) (line_of ega b r (_ : ¬b = r)))
      apply d1.prop b r (lem0.right)
    -- end of lem2 proof

    --lem3 (PROVED) : line passing thru d1(p) parallel to (p+x)
              --  and line passing thru d2(p) parallel to (p+x)
              --      are the same line as d1(p) = d2(p)
    have lem3q : ega.para_line_playfair (d1.func b) (ega.line_of b r (lem0.right)) = ega.para_line_playfair (d2.func b) (ega.line_of b r (lem0.right)) := by rw[hypab.right]
    -- end of lem3 proof

    -- lem4 : same as lem2 but for d2(x)
    have lem4q : ega.lies_on x2 (ega.para_line_playfair (d2.func b) (ega.line_of b r (lem0.right))) := by
      show EmilGeometry.lies_on ega.toEmilGeometry (d2.func r) (ega.para_line_playfair (d2.func b) (line_of ega b r (_ : ¬b = r)))
      apply d2.prop b r (lem0.right)
    -- end of lem4 proof

    -- lem5 : x1, x2 both lie on the same line parallel to (p+x)
    have lem5q : ega.lies_on x2 (ega.para_line_playfair (d2.func b) (ega.line_of b r (lem0.right))) 
    ∧ ega.lies_on x1 (ega.para_line_playfair (d2.func b) (ega.line_of b r (lem0.right))) := by
      apply And.intro
      case left => apply lem4q
      case right => 
        simp
        rw[<-lem3q]
        apply lem2q
    -- end of lem5 proof
    
    -- the common line between x1 and x2 parallel to (p+x) and (q+x)
    let lp := ega.para_line_playfair (d2.func a) (ega.line_of a r (lem0.left))
    let lq := ega.para_line_playfair (d2.func b) (ega.line_of b r (lem0.right))

    -- lem_not_parallel: lp, lq are not parallel to each other
    have lem_not_parallel : ¬ ega.is_parallel lp lq := by
      have lem11 : ega.is_parallel lp (ega.line_of a r (lem0.left)) := by
        simp 
        apply para_symm
        apply (ega.axiom2 (d2.func a) (ega.line_of a r (lem0.left))).left.right 
      have lem2 : ega.is_parallel lq (ega.line_of b r (lem0.right)) := by
        simp 
        apply para_symm
        apply (ega.axiom2 (d2.func b) (ega.line_of b r (lem0.right))).left.right 
      by_contra contra1
      have lem3 :  EmilGeometry.is_parallel lp (line_of ega b r (lem0.right)) := by
        apply ega.para_trans lp lq (line_of ega b r (lem0.right)) contra1 lem2
      
      have lem4 : ega.is_parallel (line_of ega b r (lem0.right)) (line_of ega a r (lem0.left)) := by
        have lem41 : ega.is_parallel (ega.line_of b r (lem0.right)) lp := by
          apply ega.para_symm lp (ega.line_of b r (lem0.right)) (by assumption)
        
        simp at lem11 lem41
        apply ega.para_trans (line_of ega b r (lem0.right)) (ega.para_line_playfair (d2.func a) (ega.line_of a r (lem0.left)))   (line_of ega a r (lem0.left)) lem41 lem11
      have lem5 : ega.is_parallel (line_of ega a r (lem0.left)) (line_of ega b r (lem0.right)) := by simp [para_symm, lem4]

      contradiction
      
    have lem_final : x1 = x2 := by
      apply ega.not_parallel_unique_point lp lq lem_not_parallel
      simp[lem5p, lem5q]
    assumption
  



/-- `Diltn_unique` states: a dilatation is uniquely defined by the image of its two points.
Syntax: `Diltn_unique p q hpq` with `p q : Point; hpq : ¬ p = q`.-/
theorem EmilGeomAxioms.Diltn_unique (p q : ega.Point) (hpq : ¬ p = q) : ∀ d1 d2 : ega.Dilatation, ((d1.func p = d2.func p) ∧ (d1.func q = d2.func q) 
→ d1 = d2) := by
  intro d1 d2 hyp
  
  ext r

  by_cases (ega.lies_on r (ega.line_of p q hpq))
  case neg =>
    apply ega.Diltn_aux_thm p q r hpq 
    simp [hyp]
    assumption

  
  case pos =>
    let ha := h
    by_cases p = r
    case pos =>
      simp[<-h, hyp]
    case neg =>
      let ⟨ s, hs ⟩ := ega.point_not_on_line p q hpq

      --lem0 is proved
      have lem0 : ¬ p = s:= by
        by_contra hps
        have lem1 : (ega.lies_on s (ega.line_of p q hpq)) := by
          rw [<-hps]
          simp[(ega.axiom1 p q hpq).left]
        contradiction
      -- end of lem0 proof


      have lem1 : ¬ ega.lies_on r (ega.line_of p s lem0) := by
        by_contra contra1
        have lem11 : ega.line_of p r h = ega.line_of p s lem0 := by
          have lem111 : ega.lies_on p (ega.line_of p s lem0) := by simp[ega.lies_on_endpoints]
          apply ega.line_of_line_eq
          simp [lem111,contra1]
        have lem12 : ega.line_of p q hpq = ega.line_of p r h := by
          apply Eq.symm
          apply ega.line_of_line_eq
          simp [ha, ega.lies_on_endpoints]
        rw [lem11] at lem12
        rw [lem12] at hs
        simp [ega.lies_on_endpoints] at hs
      

        
      
      -- lem2 : states that 
      -- d1(s) = d2(s).
      have lem2 : d1.func s = d2.func s := by
        apply ega.Diltn_aux_thm p q s hpq
        simp [ hyp]
        assumption
      
      apply ega.Diltn_aux_thm p s r lem0
      simp [lem2, hyp]
      assumption



/--Degenerate dilatation: when the dilatation maps all points to a single point-/
theorem EmilGeomAxioms.Diltn_deg (p q : ega.Point) (hpq : ¬ p = q) (d : ega.Dilatation) : (d.func p = d.func q) → (∀ r : ega.Point, d.func r = d.func p) := by
  intro hyp r
  let f : ega.Dilatation := {func := (fun _ ↦ d.func p), prop := (by 
  intro p1 p2 h12
  simp[ega.axiom2])}

  have lem1 : d = f := by
    apply ega.Diltn_unique p q hpq
    simp [hyp]
  rw[lem1]


/-- when the dilatation is one-one -/
theorem EmilGeomAxioms.Diltn_oneone_iff (p q : ega.Point) (hpq : ¬ p = q) (d : ega.Dilatation) : (d.func p ≠ d.func q) ↔ (∀ r1 r2 : ega.Point, d.func r1 = d.func r2 → r1 = r2) := by
  apply Iff.intro
  case mp =>
    intro hyp
    intro r1 r2 h12
    by_contra h
    have lem1 : ∀ r : ega.Point, d.func r = d.func r1 := by
      apply ega.Diltn_deg r1 r2 h
      assumption
    have lem2 : d.func p = d.func q := by
      simp [lem1]
    contradiction
  case mpr =>
    intro hyp
    by_contra h 
    have lem1 : p = q := by 
      apply hyp
      assumption
    contradiction




/--The trivial dilatation sends every point to one point-/
def EmilGeomAxioms.triv_dil (a : ega.Point) : ega.Dilatation := {
  func := fun _ => a,
  prop := ( by
    intro p1 p2 h
    simp [axiom2] )
}

/--Dilations send a line to a line parallel to it-/
theorem EmilGeomAxioms.dil_line_to_para_line (d : ega.Dilatation) (p q : ega.Point) (h : p ≠ q) (h' : d.func p ≠ d.func q) : ega.is_parallel (ega.line_of (d.func p) (d.func q) h')
(ega.line_of p q h) := by
  have h1 : ega.is_parallel (ega.line_of p q h) (ega.para_line_playfair (d.func p) (ega.line_of p q h)) := by
    simp [axiom2]
  have h2 : ega.lies_on (d.func q) (ega.para_line_playfair (d.func p) (ega.line_of p q h)) := d.prop p q h
  have h3 : ega.line_of (d.func p) (d.func q) h' = ega.para_line_playfair (d.func p) (ega.line_of p q h) := by
    apply (ega.axiom1 (d.func p) (d.func q) h').right
    apply And.intro
    case a.left =>
      simp [axiom2]
    case a.right =>
      assumption
  rw [h3]
  apply para_symm
  assumption


/--composition of dilatation-/
abbrev EmilGeomAxioms.comp_dil (d1 d2  : ega.Dilatation) : ega.Dilatation :=
  {func := fun p => d1.func (d2.func p), prop := ( by
    simp
    intro p1 p2 h
    have _ : ega.lies_on (d2.func p2) (ega.para_line_playfair (d2.func p1) 
    (p1 +! p2 -! h)) := d2.prop p1 p2 h
    by_cases h2 : d2.func p1 = d2.func p2
    case pos =>
      have h3 : d1.func (d2.func p2) = d1.func (d2.func p1) := by
        rw [h2]
      rw [h3]
      simp [axiom2]
    case neg =>
      have h3 : ega.lies_on (d1.func (d2.func p2)) (ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2)) := by
        apply d1.prop (d2.func p1) (d2.func p2) h2
      have h4 : ega.is_parallel (p1 +! p2 -! h) (ega.line_of (d2.func p1) (d2.func p2) h2) := by 
        apply para_symm 
        apply ega.dil_line_to_para_line d2 p1 p2 h h2
      have h5 : ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2) = ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of p1 p2 h) := by
        let m := ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2)
        have h5' : ega.lies_on (d1.func (d2.func p1)) m := by
          simp [axiom2]
        have h5'' : ega.is_parallel m (ega.line_of (d2.func p1) (d2.func p2) h2) := by
          simp [axiom2]
          apply ega.para_symm
          apply (ega.axiom2 (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2)).left.right
        have h6 : ega.is_parallel m (ega.line_of p1 p2 h) := by
          apply ega.para_trans m (ega.line_of (d2.func p1) (d2.func p2) h2) (ega.line_of p1 p2 h)  h5''
          apply para_symm
          assumption
        simp [eq_comm]
        apply ega.para_line_playfair_def (d1.func (d2.func p1)) (ega.line_of p1 p2 h) m h5'
        apply ega.para_symm
        assumption
      rw [<-h5]
      assumption )
      }


def EmilGeomAxioms.dil_two_points (p q p' q' : ega.Point) (h : ¬ p = q) : ega.Dilatation := {
  func := by
    intro r
    by_cases hp : r = p
    
    case pos =>
      exact p'
    
    case neg =>
      by_cases hq : r = q
      
      case pos =>
        exact q'
      
      case neg =>
        let fnotlie (s t : ega.Point) (hpt : ¬ p = t) : ¬ ega.lies_on s (ega.line_of p t hpt) → ega.Point := by
          intro h1
          have hsp : ¬ s = p := by
            by_contra contra
            rw [contra] at h1
            simp [axiom1] at h1
          have hst : ¬ s = t := by
            by_contra contra
            rw [contra] at h1
            simp [axiom1] at h1
          have h2 : ¬ ega.is_parallel (ega.line_of s p hsp) (ega.line_of s t hst) := by
            unfold EmilGeometry.is_parallel
            simp [not_or]
            apply And.intro
            
            case left =>
              by_contra contra
              let lps := ega.line_of s p hsp
              have h2 : ega.lies_on s lps := by
                simp [axiom1]
              have h3 : ega.lies_on p lps := by
                simp [axiom1]
              have h4 : ega.lies_on t (ega.line_of s t hst) := by
                simp [axiom1]
              have h5 : ega.lies_on t lps := by
                simp [*]
              have h6 : lps = ega.line_of p t hpt := by
                let hax1 := (ega.axiom1 p t hpt).right lps
                simp [eq_comm]
                apply hax1
                apply And.intro
                case left =>
                  assumption
                case right =>
                  assumption
              rw [h6] at h2
              contradiction
            
            case right =>
              have h2 : ega.lies_on s (ega.line_of s p hsp) := by
                simp [axiom1]
              have h3 : ega.lies_on s (ega.line_of s t hst) := by
                simp [axiom1]
              apply Exists.intro s
              apply And.intro
              case left =>
                assumption
              case right =>
                assumption
          
          let lp := ega.para_line_playfair p' (ega.line_of s p hsp)
          let lt := ega.para_line_playfair q' (ega.line_of s t hst)
          have hlpt : ¬ ega.is_parallel lp lt := by
            by_contra contra
            let ha := ega.para_trans (ega.line_of s p hsp) lp lt (by simp [axiom2]) contra
            let hb := ega.para_trans (ega.line_of s p hsp) lt (ega.line_of s t hst) ha (by
              apply para_symm
              simp [axiom2])
            contradiction
          
          exact (ega.Intersection lp lt hlpt)

        by_cases hlie : ega.lies_on r (ega.line_of p q h)
        case neg =>
          exact (fnotlie r q h hlie)

        case pos =>
          let s := ega.point_ax3 p q h
          have hs : ¬ ega.lies_on s (ega.line_of p q h) := by
            simp [point_ax3_prop]
          have hsp : ¬ p = s := by
            by_contra contra
            rw [<-contra] at hs
            simp [axiom1] at hs
          let s' := fnotlie s q h hs
          have hrps : ¬ ega.lies_on r (ega.line_of p s hsp) := by
            by_contra contra
          
            let prq := ega.line_of_line_eq r p hp (ega.line_of p q h) (And.intro hlie (ega.axiom1 p q h).left.left)
            let prs := ega.line_of_line_eq r p hp (ega.line_of p s hsp) (And.intro contra (ega.axiom1 p s hsp).left.left)
            rw [prq] at prs
            have slie : ega.lies_on s (ega.line_of p s hsp) := (ega.axiom1 p s hsp).left.right
            rw [<-prs] at slie
            contradiction
          
          exact (fnotlie r s hsp hrps)

  , prop := by
      sorry

}


/--structure for the non-trivial dilatations: which don't map all points to the same point-/
structure EmilGeomAxioms.nt_Dilatation extends ega.Dilatation where
  nt_prop : ∀ p1 p2 : ega.Point, (h12 : ¬ p1 = p2) →
    ¬ func p1 = func p2


/--extensionality for nt_Dilatation -/
@[ext] theorem EmilGeomAxioms.nt_Dilatation.ext (d1 d2 : ega.nt_Dilatation) : d1.func = d2.func → d1 = d2 := by
  intro hyp
  cases d1
  cases d2
  simp
  ext x
  rw [hyp]



/--auxiliary theorem for nt_Dilatation_onto.
Suppose `d : nt_Dilatation` maps distinct points `a b : Point` to `da db` respectively. If `dr : Point` does not lie on `line_of da db : Line`, then there is a pre-image of `dr` under `d`. This is used for the `nt_Dilatation_onto` theorem.-/
theorem EmilGeomAxioms.onto_aux_thm (a b dr : ega.Point) (hab : ¬ a = b) (d : ega.nt_Dilatation) :
let da := d.func a
let db := d.func b
¬ ega.lies_on dr (ega.line_of da db (by apply d.nt_prop a b hab)) → ∃ s : ega.Point, d.func s = dr := by
  intro da db hdrdadb
  have hdadb : ¬ da = db := by apply d.nt_prop a b hab
  have hdadr_dbdr : ¬ da = dr ∧ ¬ db = dr:= by apply ega.point_not_on_line_not_eq da db dr hdadb hdrdadb
  let ldadr := ega.line_of da dr hdadr_dbdr.left 
  let ldbdr := ega.line_of db dr hdadr_dbdr.right
  let ldadb := ega.line_of da db hdadb
  let lab := ega.line_of a b hab
  
  have not_para_1 : ¬ ega.is_parallel ldadr ldbdr := by 
    simp [ega.point_not_on_line_not_parallel, hdadb, hdrdadb]

  let l1a := ega.para_line_playfair a ldadr
  let l2b := ega.para_line_playfair b ldbdr

  have para_lem11 :  ega.is_parallel l1a ldadr := by
    simp
    apply para_symm
    apply (ega.axiom2 a ldadr).left.right
  
  have para_lem12 : ega.is_parallel l2b ldbdr := by
    simp
    apply para_symm
    apply (ega.axiom2 b ldbdr).left.right
  


  have not_para_2 : ¬ ega.is_parallel l1a l2b := by 
    by_contra contra1
    
    have lem13 : ega.is_parallel l1a ldbdr := by
      apply para_trans l1a l2b ldbdr contra1 para_lem12
    have lem14 : ega.is_parallel ldadr l1a := by
      apply para_symm
      assumption
    have lem15 : ega.is_parallel ldadr ldbdr := by
      apply para_trans ldadr l1a ldbdr lem14 lem13
    simp [lem15] at not_para_1
  
      

  let ⟨ s, hs ⟩ := ega.not_parallel_common_point l1a l2b not_para_2

  have lem11 : ega.para_line_playfair da l1a = ldadr := by 
    apply ega.para_line_playfair_def da l1a ldadr (by simp[ega.lies_on_endpoints]) 
    assumption
      
  have lem13 : ega.para_line_playfair db l2b = ldbdr := by
    apply ega.para_line_playfair_def db l2b ldbdr (by simp[ega.lies_on_endpoints]) 
    assumption

  
  have lem_main : ¬ ega.lies_on s lab := by 
    by_contra contra1

    have lem_main1 : lab = l1a ∨ lab = l2b := by
      by_cases h123 : a = s 
      case pos =>
        rw [<-h123] at hs
        have lem123 : ega.lies_on b l2b := by
          apply (ega.axiom2 b ldbdr).left.left
        have lem124 : ega.lies_on a l2b := by
          apply hs.right
        have lem125 : lab = l2b := by
          apply ega.line_of_line_eq
          simp [lem123, lem124]
        simp[lem125]
      case neg =>
        have lem123 : ega.line_of a s h123 = lab := by
          apply ega.line_of_line_eq
          simp [contra1, ega.lies_on_endpoints]
        have lem124 : ega.lies_on s l1a := by
          apply hs.left
        have lem125 : ega.line_of a s h123 = l1a := by
          apply ega.line_of_line_eq
          apply And.intro
          case a.left =>
            apply (ega.axiom2 a ldadr).left.left
          case a.right =>
            apply lem124
        have lem126 : lab = l1a := by
          apply Eq.symm
          rw[<-lem125]
          assumption
        simp[lem126]

    have lemm : ¬ ega.is_parallel ldadb ldadr := by
        by_contra contra2
        apply Or.elim contra2
        case left =>
          intro hyp1
          have lem_1 : ega.lies_on dr ldadr := by
            simp [ega.lies_on_endpoints]
          rw[<-hyp1] at lem_1
          contradiction
        case right =>
          intro hyp1
          have yesr1 :  ega.lies_on da ldadb := by
            simp[ega.lies_on_endpoints]
          have yesr2 : ega.lies_on da ldadr := by
            simp[ega.lies_on_endpoints]
          have notr : ¬ ega.lies_on da ldadr := by
            simp[yesr1, hyp1]
          contradiction
    have lemm2 : ¬ega.is_parallel ldadb ldbdr := by
      by_contra contra2
      apply Or.elim contra2
      case left =>
        intro hyp1
        have lem_1 : ega.lies_on dr ldbdr := by
          simp [ega.lies_on_endpoints]
        rw[<-hyp1] at lem_1
        contradiction
      case right =>
        intro hyp1
        have yesr1 :  ega.lies_on db ldadb := by
          simp[ega.lies_on_endpoints]
        have yesr2 : ega.lies_on db ldbdr := by
          simp[ega.lies_on_endpoints]
        have notr : ¬ ega.lies_on db ldbdr := by
          simp[yesr1, hyp1]
        contradiction

    have lemm3 : ega.is_parallel lab ldadb := by
      
      have lemme1 : ega.lies_on db ((para_line_playfair ega (Dilatation.func d.toDilatation a) (line_of ega a b hab))) := by
        apply d.prop a b hab 
      have lemme2 : (para_line_playfair ega (da) (line_of ega a b hab)) = ldadb := by
        apply Eq.symm
        have lem' : ega.lies_on da (para_line_playfair ega (da) (line_of ega a b hab)) := by
          apply (ega.axiom2 da lab ).left.left
        apply ega.line_of_line_eq 
        simp [lem', lemme1]
      rw [<-lemme2]
      apply (ega.axiom2 da lab ).left.right
        

    apply Or.elim lem_main1
    case left =>
      intro the_hyp

      rw[<-the_hyp] at para_lem11
      have para_not : ega.is_parallel ldadb ldadr := by
        have para_not1 : ega.is_parallel ldadb lab := by
          apply para_symm
          assumption
        apply ega.para_trans ldadb lab ldadr para_not1
        apply para_lem11
      contradiction
    case right =>
      intro the_hyp
      rw[<-the_hyp] at para_lem12
      have para_not : ega.is_parallel ldadb ldbdr := by
        have para_not1 : ega.is_parallel ldadb lab := by
          apply para_symm
          assumption
        apply ega.para_trans ldadb lab ldbdr para_not1
        apply para_lem12
      contradiction
  
  have lem_main2 : ¬ a = s := by
    apply (ega.point_not_on_line_not_eq a b s hab lem_main).left
  
  let ds := d.func s
  have lem12 : ega.lies_on ds ldadr := by 
    let las := ega.line_of a s lem_main2
    have lemm1 : las = l1a := by
      apply ega.line_of_line_eq
      simp [hs]
      simp [ega.axiom2]
    have lemm2 : ega.lies_on ds (ega.para_line_playfair da las) := by
      apply d.prop
    rw[<-lemm1] at lem11
    rw[lem11] at lemm2
    assumption


  have lem_main3 : ¬b = s := by
    apply (ega.point_not_on_line_not_eq a b s hab lem_main).right

  have lem14 : ega.lies_on ds ldbdr := by 
    let lbs := ega.line_of b s lem_main3
    have lemm1 : lbs = l2b := by
      apply ega.line_of_line_eq
      simp [hs]
      simp [ega.axiom2]
    have lemm2 : ega.lies_on ds (ega.para_line_playfair db lbs) := by
      apply d.prop
    rw[<-lemm1] at lem13
    rw[lem13] at lemm2
    assumption
  
  
    

  have lem1 : dr = d.func s := by    
    apply ega.not_parallel_unique_point ldadr ldbdr not_para_1
    simp [lem12, lem14, ega.lies_on_endpoints]
  
  rw[lem1]
  apply Exists.intro s
  rfl



/--any nt_dilatation.func is onto function-/
theorem EmilGeomAxioms.nt_Dilatation_onto (d : ega.nt_Dilatation) : (∀ r : ega.Point, ∃r0 : ega.Point, d.func r0 = r) := by
  intro dr
  let ⟨a, b, c, hyp, _⟩  := ega.axiom3
  let da := d.func a
  let db := d.func b
  have lem : ¬ da = db := by apply d.nt_prop a b (hyp.left)

  
  by_cases (dr = da ∨ dr = db)
  case pos =>
    apply Or.elim h
    case left => 
      intro h1
      simp[h1]
    case right =>
      intro h2
      simp [h2]
  case neg =>
    rw[not_or] at h 
    

    let ldrda := ega.line_of dr da (h.left)
    
    let ldadb := ega.line_of da db (lem)
    

    by_cases (ega.lies_on dr ldadb)
    case neg =>
      apply ega.onto_aux_thm a b dr (hyp.left) d h 
    case pos =>
      let hrl := h
      by_cases dr = da
      case pos =>
        simp [h]
      case neg =>
        let ⟨ ds, hds ⟩ := ega.point_not_on_line da db lem

        have hdads : ¬ da = ds := by 
          apply (ega.point_not_on_line_not_eq da db ds lem hds).left
        have lem_find_s : ∃ s : ega.Point, d.func s = ds := by
          apply ega.onto_aux_thm a b ds hyp.left d
          assumption
        let ⟨ s, hs ⟩ := lem_find_s
        have hasl : ¬ a = s := by 
          by_contra contra1
          rw[<-contra1] at hs 
          rw[<-hs] at hdads
          simp at hdads
        
        have ldrdads : ¬ ega.lies_on dr (ega.line_of da ds hdads) := by 
          by_contra contra1
          have lem11 : ldrda = ega.line_of da ds hdads := by
            apply ega.line_of_line_eq
            simp [contra1, ega.lies_on_endpoints]
          have lem12 : ldrda = ldadb := by 
            apply ega.line_of_line_eq
            simp [hrl, ega.lies_on_endpoints]
          simp[lem11] at lem12
          rw[<-lem12] at hds
          simp[ega.lies_on_endpoints] at hds 
        apply ega.onto_aux_thm a s dr hasl d
        simp [<-hs] at ldrdads
        by_contra contra2
        contradiction

       





/--The identity dilatation-/
def EmilGeomAxioms.id_dil : ega.nt_Dilatation := 
    { 
      func := fun p => p,
      
      prop := (by
        intro p1 p2 h
        simp
        have h1 : ega.para_line_playfair p1 (line_of ega p1 p2 h) = line_of ega p1 p2 h := by
          apply para_line_playfair_is_same
          simp [axiom1]
        rw [h1]
        simp[axiom1]),
      
      nt_prop := (by
       intro p1 p2 h
       simp
       assumption)
    }


/--nt_Dilations send a line to a line parallel to it-/
theorem EmilGeomAxioms.nt_dil_line_to_para_line (d : ega.nt_Dilatation) (p q : ega.Point) (h : p ≠ q) (h' : d.func p ≠ d.func q) : ega.is_parallel (ega.line_of (d.func p) (d.func q) h')
(ega.line_of p q h) := by
  have h1 : ega.is_parallel (ega.line_of p q h) (ega.para_line_playfair (d.func p) (ega.line_of p q h)) := by
    simp [axiom2]
  have h2 : ega.lies_on (d.func q) (ega.para_line_playfair (d.func p) (ega.line_of p q h)) := d.prop p q h
  have h3 : ega.line_of (d.func p) (d.func q) h' = ega.para_line_playfair (d.func p) (ega.line_of p q h) := by
    apply (ega.axiom1 (d.func p) (d.func q) h').right
    apply And.intro
    case a.left =>
      simp [axiom2]
    case a.right =>
      assumption
  rw [h3]
  apply para_symm
  assumption




/--composition of two non-trivial dilatations-/
abbrev EmilGeomAxioms.nt_Dilatation_comp (d1 d2 : ega.nt_Dilatation) : ega.nt_Dilatation :=
  {func := fun p => d1.func (d2.func p), prop := ( by
    simp
    intro p1 p2 h
    have _ : ega.lies_on (d2.func p2) (ega.para_line_playfair (d2.func p1) 
    (p1 +! p2 -! h)) := d2.prop p1 p2 h
    by_cases h2 : d2.func p1 = d2.func p2
    case pos =>
      have h3 : d1.func (d2.func p2) = d1.func (d2.func p1) := by
        rw [h2]
      rw [h3]
      simp [axiom2]
    case neg =>
      have h3 : ega.lies_on (d1.func (d2.func p2)) (ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2)) := by
        apply d1.prop (d2.func p1) (d2.func p2) h2
      have h4 : ega.is_parallel (p1 +! p2 -! h) (ega.line_of (d2.func p1) (d2.func p2) h2) := by 
        apply para_symm 
        apply ega.nt_dil_line_to_para_line d2 p1 p2 h h2
      have h5 : ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2) = ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of p1 p2 h) := by
        let m := ega.para_line_playfair (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2)
        have h5' : ega.lies_on (d1.func (d2.func p1)) m := by
          simp [axiom2]
        have h5'' : ega.is_parallel m (ega.line_of (d2.func p1) (d2.func p2) h2) := by
          simp [axiom2]
          apply ega.para_symm
          apply (ega.axiom2 (d1.func (d2.func p1)) (ega.line_of (d2.func p1) (d2.func p2) h2)).left.right
        have h6 : ega.is_parallel m (ega.line_of p1 p2 h) := by
          apply ega.para_trans m (ega.line_of (d2.func p1) (d2.func p2) h2) (ega.line_of p1 p2 h)  h5''
          apply para_symm
          assumption
        simp [eq_comm]
        apply ega.para_line_playfair_def (d1.func (d2.func p1)) (ega.line_of p1 p2 h) m h5'
        apply ega.para_symm
        assumption
      rw [<-h5]
      assumption ),
    nt_prop := (by
      simp
      intro p1 p2 h
      have h1 : ¬ d2.func p1 = d2.func p2 := by
        apply d2.nt_prop p1 p2 h
      apply d1.nt_prop (d2.func p1) (d2.func p2) h1
      )}





instance : Group (ega.nt_Dilatation) where
  -- a * b
  mul := ega.nt_Dilatation_comp
  
  one := ega.id_dil

  -- 1 * a = a
  one_mul := by
    intro a
    ext x
    show (nt_Dilatation_comp a id_dil).func x = a.func x
    simp [id_dil]
  
  -- a * 1 = a
  mul_one := by
    intro a
    ext x
    show (nt_Dilatation_comp a id_dil).func x = a.func x
    simp [id_dil]
  
  inv := sorry

  mul_left_inv := by 
    intro a 
    ext x
    sorry

    
  --a*b*c = a*(b*c)
  mul_assoc := by
    intro a b c
    ext x
    show (nt_Dilatation_comp (nt_Dilatation_comp a b) c).func x = (nt_Dilatation_comp a (nt_Dilatation_comp b c)).func x
    simp


