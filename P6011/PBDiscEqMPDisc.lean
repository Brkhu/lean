import Brkhu.P6011.YTheta

set_option linter.style.emptyLine false

open NumberField


noncomputable abbrev pb : Fin 3 → 𝓞 F := fun n => yO ^ n.val

theorem discr_powbase_eq_discr_minpoly : f.discr = Algebra.discr ℤ pb := by

  sorry
