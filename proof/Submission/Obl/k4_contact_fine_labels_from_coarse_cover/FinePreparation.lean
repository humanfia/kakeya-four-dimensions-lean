import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.FineAssembly
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBudget
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.StatementGlue

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Submission.Lib.K4QuadraticSheetCore

open Set Filter MeasureTheory
open Submission.Lib.K4ContactNormalization

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- The three-entry palettes cover the original incidence law almost everywhere at every sufficiently shallow depth. -/
theorem preparation (hp : p.Valid) (hcoarse : p.CoarseCover) :
    ∃ U₁ : ℝ, 0 < U₁ ∧ U₁ ≤ p.U ∧ ∀ s : ℝ, 0 < s → s ≤ U₁ →
      depthPrepared p.N p.K p.μ p.b p.T p.n p.j p.B s := by
  obtain ⟨H, hH, hHsub, hcover⟩ := hcoarse
  obtain ⟨U₁, hU₁, hU₁U, hrange⟩ := exists_fine_depth_range p hp
  refine ⟨U₁, hU₁, hU₁U, ?_⟩
  intro s hs hsU₁ ε η hε hη
  obtain ⟨hsU, hdeep, he₀⟩ := hrange s hs hsU₁
  let v : ℝ := min ε s / 1000
  have hv : 0 < v := div_pos (lt_min hε hs) (by norm_num)
  have hve : 240 * v < ε := by
    have := min_le_left ε s
    dsimp [v]
    linarith
  have hvs : 240 * v < s := by
    have := min_le_right ε s
    dsimp [v]
    linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  have hcard : ∀ᶠ k in atTop, (3 : ℝ) ≤ p.N k ^ ε :=
    ((tendsto_rpow_atTop hε).comp hp.N_lim).eventually (eventually_ge_atTop 3)
  filter_upwards [eventually_fine_palette p hp H hH hHsub hcover hs hdeep le_rfl hv hvs he₀,
    eventually_fine_loss p.N p.K H hN1 hp.N_lim hp.K_ge hH hp.K_sub hHsub
      (le_trans zero_le_one one_le_paletteConst) hve, hcard] with k hpal hloss hcard
  obtain ⟨L, hL⟩ := hpal
  refine ⟨3, L, hcard, ?_⟩
  have hgood : ∀ᵐ u ∂p.μ k, u ∈
      paletteEvent (fun l t => point (p.b k l) t) (p.B k s)
        (fun i => p.I k s i) L (p.a k s) (p.N k ^ ε) :=
    hL.mono (fun u hu => paletteEvent_mono (fun l t => point (p.b k l) t)
      (p.B k s) (fun i => p.I k s i) L (Valid.a_pos p hp k s).le hloss hu)
  have hzero : p.μ k (paletteEvent (fun l t => point (p.b k l) t) (p.B k s)
      (fun i => p.I k s i) L (p.a k s) (p.N k ^ ε))ᶜ = 0 := ae_iff.mp hgood
  change p.μ k (paletteEvent (fun l t => point (p.b k l) t) (p.B k s)
    (fun i => p.I k s i) L (p.a k s) (p.N k ^ ε))ᶜ ≤ _
  rw [hzero]
  exact bot_le

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
