-- From this LOT tree, o241, session x0881, commit 8b736ce8, SplitClosure.lean.
import Submission.Obl.k4_contact_equal_rate_affine_palettes.SplitStatements
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.DepthPreparation

namespace Submission.Obl.k4_contact_equal_rate_affine_palettes

/-- Coarse native approximation, fine-label preparation and the proved finite-depth
mass/subpower assembly close the frozen theorem. -/
theorem split_closure (hNative : NativeCoarseStatement) (hFine : FineLabelStatement) :
    FrozenStatement := by
  intro N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hκℓ hS0 hS1 hU0 he₀0
    hregime hhorizontal α inst ν μ ρ π b P T n j A B c F
    hcontact hBasic hCaps hLabels hNested hEqual
  have hcoarse := hNative N K hN hNt hK d S e₀ hd0 hd1 hS0 hS1 he₀0
    α ν μ ρ π b P hcontact hBasic hCaps
  obtain ⟨U₁, hU₁, hU₁U, hdepth⟩ := hFine N K hN hNt hK
    d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hκℓ hS0 hS1 hU0 he₀0
    hregime hhorizontal α ν μ ρ π b P T n j A B c F
    hcontact hBasic hCaps hLabels hNested hEqual hcoarse
  exact Submission.Obl.k4_contact_fine_labels_from_coarse_cover.finite_palettes_of_depth_prepared N K
    (fun k => le_trans (by norm_num) (hN k))
    (fun k => lt_of_lt_of_le zero_lt_one (hK.1 k)) μ ρ
    (fun k => (hBasic k).2.2.2.2.1)
    (fun k => (hBasic k).2.2.2.2.2.2.1)
    b T n j B hU₁ hU₁U hdepth

end Submission.Obl.k4_contact_equal_rate_affine_palettes
