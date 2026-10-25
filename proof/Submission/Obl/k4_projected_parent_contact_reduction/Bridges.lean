import Submission.Obl.k4_projected_parent_contact_reduction.Interfaces

/-! Definitional bridges between the compressed child interfaces and the frozen goal. -/

namespace Submission.Obl.k4_projected_parent_contact_reduction.Split

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem contact_mode (h : ContactPrinciple) : Problem 3 := by
  intro N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hS0 hS1 hU he₀
    hreg hhor α inst ν μ ρ π b P T n j A B c F hcontact
  exact h N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 trivial
    hS0 hS1 hU he₀ hreg hhor α ν μ ρ π b P T n j A B c F (hcontact rfl)

theorem general_mode (h : Problem 2) : GeneralPrinciple := by
  intro N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hS0 hS1 hU he₀
    hreg hhor α inst ν μ ρ π b P T n j A B c F
  exact h N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0
    hS0 hS1 hU he₀ hreg hhor α ν μ ρ π b P T n j A B c F (by
      intro hbad
      cases hbad)

end Submission.Obl.k4_projected_parent_contact_reduction.Split
