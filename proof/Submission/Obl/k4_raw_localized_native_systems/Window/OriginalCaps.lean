import Submission.Obl.k4_raw_localized_native_systems.Window.RawBounds
import Submission.Obl.k4_uncapped_native_capping.PacketCapBounds
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeBaseCeiling

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The accepted original-cap package uses the same exact problem data. -/
def originalCapProblem (p : Data) : k4_uncapped_native_capping.UWE.Problem :=
  ⟨p.N, p.K, p.L, p.d, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

/-- The common analytical original law has a zero-depth base cap, with no
conditioning or profile-offset bound. -/
theorem original_zero_base_cap {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    (ρ : Measure Point) (hρ : ρ ≤ selected p k γ) {κ τ : ℝ}
    (hκ : 1 ≤ κ) (hKκ : p.K k ≤ κ)
    (htyp : ∀ᵐ z ∂ρ, p.g k γ 0 (obs (p.B k γ) 1 z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f 0 + τ))) :
    Measure.map basePt ρ ≤
      (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) * ENNReal.ofReal (64 * κ ^ 2)) • volume := by
  have hp' : (originalCapProblem p).Valid p.S p.η := hp
  have hn := k4_uncapped_native_capping.PacketCapBounds.ae_native_bounds hp' k γ hKκ
  have hP := native_bounds_ae hp k γ (p.E k γ) (valid_E_meas hp k γ) Subset.rfl
  have hP' : ∀ᵐ z ∂selected p k γ, |MvPolynomial.eval (x z.1 z.2) (p.P k γ)| ≤ κ :=
    hP.mono fun z hz => hz.1.trans hKκ
  have hn' := (ae_mono hρ) hn
  have hPρ := (ae_mono hρ) hP'
  obtain ⟨hgm, hlaw⟩ := valid_g_law hp k γ le_rfl hp.length_pos.le
  rw [delta_zero] at hlaw
  apply k4_uncapped_native_capping.UWE.native_zero_depth_base_ceiling
    (selected p k γ) ρ hρ hκ (hp.B_pos k γ) (p.P k γ) (valid_P_degree hp k γ)
    (p.g k γ 0) hgm hlaw (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)))
  filter_upwards [hn', hPρ, htyp] with z hz hPz htz
  exact ⟨hz.1, hz.2.1, hPz, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, htz⟩

/-- A common measurable density mask supplies the original-law cap used in
full earlier-witness packing. -/
theorem masked_original_zero_base_cap {p : Data} (hp : Valid p) (k : ℕ)
    (γ : Fin (p.W k)) {κ τ : ℝ} (hκ : 1 ≤ κ) (hKκ : p.K k ≤ κ)
    (Good : Set Point) (hm : MeasurableSet Good)
    (htyp : ∀ z ∈ Good, p.g k γ 0 (obs (p.B k γ) 1 z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f 0 + τ))) :
    Measure.map basePt ((selected p k γ).restrict Good) ≤
      ENNReal.ofReal (64 * κ ^ 2 * p.N k ^ (-p.f 0 + τ)) • volume := by
  have hgood : ∀ᵐ z ∂(selected p k γ).restrict Good,
      p.g k γ 0 (obs (p.B k γ) 1 z) ≤ ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) := by
    filter_upwards [ae_restrict_mem hm] with z hz
    exact htyp z hz
  have hh := original_zero_base_cap hp k γ ((selected p k γ).restrict Good)
    Measure.restrict_le_self hκ hKκ hgood
  have hN := hp.scale_pos k
  convert hh using 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

end
end Submission.Obl.k4_raw_localized_native_systems.Window
