/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameLaw.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameCoordinates
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.NormalizedLaw
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ContactBaseBounds

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open Set MeasureTheory ProbabilityTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_critical_affine_derivative_preparation

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (fr : Frame D k s₀ U')

theorem resρ_le_resμ (hρ : D.ρ k ≤ D.μ k) : fr.resρ ≤ fr.resμ := by
  exact smul_le_smul_left _ (Measure.map_mono
    (Measure.restrict_mono_measure hρ fr.core) fr.measurable_toChart)

theorem resρ_univ : fr.resρ univ = fr.scale⁻¹ * D.ρ k fr.core := by
  rw [resρ, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply fr.measurable_toChart MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

theorem resρ_mass_floor {m : ENNReal} (hscale : fr.scale ≠ 0)
    (hscale_top : fr.scale ≠ ⊤) (hmass : m * fr.scale ≤ D.ρ k fr.core) :
    m ≤ fr.resρ univ := by
  rw [fr.resρ_univ]
  calc
    m = (fr.scale⁻¹ * fr.scale) * m := by
      rw [ENNReal.inv_mul_cancel hscale hscale_top, one_mul]
    _ = fr.scale⁻¹ * (m * fr.scale) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hmass

theorem resμ_domination [IsFiniteMeasure (D.ν k)]
    (hK : 0 ≤ D.K k) (hA : D.ν k fr.parentSet ≠ 0)
    (hcore : fr.core ⊆ fr.parentSet ×ˢ (univ : Set ℝ))
    (hdom : D.μ k ≤ ENNReal.ofReal (D.K k) • (D.ν k).prod volume) :
    fr.resμ ≤ ENNReal.ofReal (D.K k) • ((cond (D.ν k) fr.parentSet).prod volume) :=
  original_parent_normalized_domination (D.ν k) (D.μ k) fr.parentSet fr.core
    fr.q₀_pos hK hA hcore hdom

theorem scale_eq_ofReal [IsFiniteMeasure (D.ν k)] :
    fr.scale = ENNReal.ofReal (fr.q₀ * (D.ν k).real fr.parentSet) := by
  rw [scale, ENNReal.ofReal_mul fr.q₀_pos.le, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top (D.ν k) fr.parentSet)]

theorem resμ_unit_support [IsFiniteMeasure (D.ν k)]
    (hA : D.ν k fr.parentSet ≠ 0)
    (hcore : fr.core ⊆ fr.event 0 fr.i₀ fr.u₀) :
    fr.resμ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hW : 0 < fr.q₀ * (D.ν k).real fr.parentSet :=
    mul_pos fr.q₀_pos (ENNReal.toReal_pos hA (measure_ne_top (D.ν k) fr.parentSet))
  have hfull : ((D.μ k).restrict fr.core) (univ ×ˢ Icc fr.t₀ (fr.t₀ + fr.q₀))ᶜ = 0 := by
    have hsub : fr.core ⊆ univ ×ˢ Icc fr.t₀ (fr.t₀ + fr.q₀) := by
      intro p hp
      exact ⟨mem_univ _, fr.parent_block ▸ (hcore hp).2⟩
    rw [Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc).compl]
    have hempty : (univ ×ˢ Icc fr.t₀ (fr.t₀ + fr.q₀))ᶜ ∩ fr.core = ∅ := by
      ext p
      constructor
      · intro hp
        exact hp.1 (hsub hp.2)
      · intro hp
        exact hp.elim
    rw [hempty, measure_empty]
  have hh := original_continuous_normalized_support ((D.μ k).restrict fr.core)
    fr.t₀ fr.q₀ (fr.q₀ * (D.ν k).real fr.parentSet) fr.q₀_pos hfull
  unfold resμ
  rw [fr.scale_eq_ofReal, ← ENNReal.ofReal_inv_of_pos hW]
  exact hh

/-- The full conditional parent prior has bounded base coefficients in the
contact chart. Row centering removes every inverse parent-scale loss. -/
theorem parent_prior_base_bound {K J g : ℝ} (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hparent : MeasurableSet fr.parentSet) (hg : g ≤ K * fr.q₀)
    (hv : ∀ᵐ l ∂D.ν k, |D.b k l 3| ≤ K)
    (hrows : ∀ l ∈ D.A k (fr.depth 0) fr.i₀,
      |(D.x k l fr.t₀) 1 - D.c k (fr.depth 0) fr.i₀ 0 -
        fr.t₀ * D.c k (fr.depth 0) fr.i₀ 1| ≤ K * fr.q₀ ∧
      |(D.x k l fr.t₀) 2 - D.c k (fr.depth 0) fr.i₀ 2 -
        fr.t₀ * D.c k (fr.depth 0) fr.i₀ 3 -
        D.c k (fr.depth 0) fr.i₀ 4 * (D.x k l fr.t₀) 1| ≤ K * fr.q₀ * g ∧
      |D.b k l 4 - D.c k (fr.depth 0) fr.i₀ 3 -
        D.c k (fr.depth 0) fr.i₀ 4 * D.b k l 3| ≤ K * g)
    (hcenter : |D.c k (fr.depth 0) fr.i₀ 3 + fr.Z₀| ≤ J * fr.q₀)
    (hpivot : |D.c k (fr.depth 0) fr.i₀ 4 - fr.t₀| ≤ J * fr.q₀) :
    ∀ᵐ l ∂cond (D.ν k) fr.parentSet,
      |fr.coeff l 0| + |fr.coeff l 1| + |fr.coeff l 3| + |fr.coeff l 4| ≤
        2 * K + 2 * K ^ 2 + 2 * J * K + J := by
  have hv' : ∀ᵐ l ∂cond (D.ν k) fr.parentSet, |D.b k l 3| ≤ K :=
    Measure.ae_smul_measure (ae_restrict_of_ae hv) ((D.ν k) fr.parentSet)⁻¹
  have hm : ∀ᵐ l ∂cond (D.ν k) fr.parentSet, l ∈ fr.parentSet :=
    Measure.ae_smul_measure (ae_restrict_mem hparent) ((D.ν k) fr.parentSet)⁻¹
  filter_upwards [hv', hm] with l hlv hl
  have hlA : l ∈ D.A k (fr.depth 0) fr.i₀ := hl.1
  obtain ⟨hr₁, hr₂, hr₃⟩ := hrows l hlA
  have hz : |D.b k l 0 + fr.t₀ * D.b k l 3 - fr.Z₀| ≤ K * fr.q₀ := by
    convert hr₁ using 1
    congr 1
    simp [Data.x, Z₀] <;> ring
  have hy : |D.b k l 1 + fr.t₀ * D.b k l 4 - fr.Y₀ -
      D.c k (fr.depth 0) fr.i₀ 4 * (D.b k l 0 + fr.t₀ * D.b k l 3 - fr.Z₀)| ≤
        K * fr.q₀ * g := by
    convert hr₂ using 1
    congr 1
    simp [Data.x, Y₀] <;> ring
  have hh := contact_base_coefficient_bound hK hJ fr.q₀_pos hg (D.b k l) hlv
    hz hy hr₃ hcenter hpivot
  simpa [coeff, residualCoeff, contactChartCoeff] using hh

/-- A parent's successful entry controls the residual hidden coordinate on
the entire normalized unit block, including times outside the retained core. -/
theorem parent_residual_bound (hN : 0 < D.N k) (l : α) (hl : l ∈ fr.parentSet)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |point (fr.coeff l) t 3| ≤ fr.H := by
  have hentry : l ∈ fr.entry 0 fr.i₀ fr.u₀ := hl.2
  have hfit : l ∈ affineFitSet (D.b k) (fr.pal 0 fr.i₀ fr.u₀)
      (fr.left 0 fr.i₀) (fr.right 0 fr.i₀) (fr.H * fr.a₀) := hentry.1.2
  have htold : fr.t₀ + fr.q₀ * t ∈ fr.block 0 fr.i₀ := by
    rw [fr.parent_block]
    have h₀ : 0 ≤ fr.q₀ * t := mul_nonneg fr.q₀_pos.le ht.1
    have h₁ : fr.q₀ * t ≤ fr.q₀ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 fr.q₀_pos.le
    constructor <;> linarith
  have hvalue := hfit (fr.t₀ + fr.q₀ * t) htold
  have htime : (fr.t₀ + fr.q₀ * t - fr.t₀) / fr.q₀ = t := by
    field_simp [fr.q₀_pos.ne'] <;> ring
  have hhidden := fr.point_coeff_hidden l (fr.t₀ + fr.q₀ * t)
  rw [htime] at hhidden
  rw [hhidden, abs_div, abs_of_pos (fr.a₀_pos hN)]
  apply (div_le_iff₀ (fr.a₀_pos hN)).mpr
  simpa only [Data.x, point, abs_sub_comm] using hvalue

end Frame

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
