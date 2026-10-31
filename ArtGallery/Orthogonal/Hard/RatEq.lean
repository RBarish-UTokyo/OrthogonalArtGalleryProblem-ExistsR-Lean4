module

public import Mathlib.Data.Rat.Defs

/-!
# Decidable equality of rationals for kernel computation

The certificates of the orthogonal construction are checked by kernel evaluation, and their checks
compare rationals (and pairs, options and lists of them) for equality.  The derived instance
`instDecidableEqRat` returns `isTrue` through casts (`Eq.ndrec`) along the equalities of the
fields; a kernel that reduces such a cast by evaluating the equality proof spends time
proportional to the compared numbers.  `Rat.decEqND` decides the equality of the numerators and
of the denominators and returns `isTrue` without a cast.  It has high priority, so every module of
the construction (each imports this one) elaborates its rational equalities with it.
-/

@[expose] public section

/-- Decidable equality of rationals by numerator and denominator. -/
instance (priority := high) Rat.decEqND : DecidableEq ℚ := fun x y =>
  if h : x.num = y.num ∧ x.den = y.den then isTrue (Rat.ext h.1 h.2)
  else isFalse fun e => h ⟨congrArg Rat.num e, congrArg Rat.den e⟩

end
