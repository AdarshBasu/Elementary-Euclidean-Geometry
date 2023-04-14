import Lake

#eval 1



class Oper (a : Type) where
  oper : a → a → a


#check Oper.oper


instance : Oper Int where
  oper := fun x y => x^2 + y^2

instance : Oper Float where
  oper := fun x y => x^2 + y^2

instance : Oper String where
  oper := fun x y => x ++ y


#eval Oper.oper "Hello" " World"
#eval Oper.oper 5.0 6
#eval Oper.oper (-5) 6
#eval Oper.oper 5 6 -- error : failed to synthesize instance Oper Nat
-- we are giving/"synthesizing" the instance above when we say :
-- instance Oper Int

#check Prop
#check Nat







/--
Integrability of `f`, i.e., given an interval `[a, b]`, we can compute the integral of `f` over that interval. Additivity over intervals is also required.
-/
class Integrable (f: ℝ → ℝ) where
  integral (a b : ℝ) : ℝ  
  interval_union (a b c : ℝ) :
    integral a c = integral a b + integral b c

/-- The integral of a function, with the typeclass derived -/
def integral (f: ℝ → ℝ)[int : Integrable f]
  (a b : ℝ ) :=
  int.integral a b

/-- The integral over a single point is zero, proved as an illustration. -/
theorem integral_point(f: ℝ → ℝ)[int : Integrable f]
  (a : ℝ ) : integral f a a = 0 := by
    unfold integral
    have l := int.interval_union a a a
    simp  at l
    assumption





