import Submission.Obl.k4_scalar_grid_cartesian_field.SourceRefinement
import Submission.Obl.k4_scalar_grid_cartesian_field.CorePacket
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreScales
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreQualification
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketCoreGeometry
import Submission.Obl.k4_scalar_grid_cartesian_field.PreparationNumerics
import Submission.Obl.k4_scalar_grid_cartesian_field.AngularBreadth

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval blockLeft_nonneg blockRight_le_one)

/-- Scalar, density and graph data left after the first source-packet pruning. -/
structure SourceCoreInput {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H H₀ : ℝ}
    (s : SourcePacket data k M G E B ε L H) {Band : Set ℝ}
    (r : SourceRefinement s H₀ Band) (Λ β rT : ℝ) (θ : Measure Trajectory) : Prop where
  hN : 2 ≤ data.N k
  hΛ : 1 ≤ Λ
  hH : 1 ≤ H
  hH₀ : 1 ≤ H₀
  budget : PreparationBudgetBounds (data.K k) L H₀ H Λ
  geometry_base : 2 * data.K k ≤ L
  geometry_layer : 3000 * data.K k ^ 3 ≤ L
  precision : CorePrecision (data.N k) Λ (packetLength data k) M B
  error_eq : fieldError (data.N k) (packetLength data k) = data.N k ^ (-rT)
  qualification_budget : data.N k ^ ε ≤ Λ
  hβ : 0 < β
  separation_budget : data.N k ^ β ≤ Λ
  band_velocity : (20 : ℝ) ∈ Band
  band_separation : β ∈ Band
  finite_ρ : IsFiniteMeasure (data.ρ k (data.γ k 1 s.i))
  finite_θ : IsFiniteMeasure θ
  measurable_E : MeasurableSet (E k (data.γ k 1 s.i))
  lower_graph_density : (θ.prod volume).restrict (E k (data.γ k 1 s.i)) ≤
    ENNReal.ofReal H₀ • (data.ρ k (data.γ k 1 s.i)).restrict (E k (data.γ k 1 s.i))
  upper_graph_density : (data.ρ k (data.γ k 1 s.i)).restrict (E k (data.γ k 1 s.i)) ≤
    ENNReal.ofReal H₀ • (θ.prod volume).restrict (E k (data.γ k 1 s.i))
  graph_bound : ∀ x ∈ E k (data.γ k 1 s.i),
    (∀ e, |G k (data.γ k 1 s.i) (physCube (data.N k) B x) e| ≤ H) ∧
    |x.1.2 3 + 2 * x.2 * x.1.2 4 - G k (data.γ k 1 s.i) (physCube (data.N k) B x) 0 -
      G k (data.γ k 1 s.i) (physCube (data.N k) B x) 1 * x.1.2 1| ≤ H * data.N k ^ (-40 : ℝ)
  coarse_lists : ∀ q : Fin 3 → ℤ, ({w : Fin 2 → ℤ | (data.ρ k (data.γ k 1 s.i)).restrict
    (E k (data.γ k 1 s.i)) {x | physCube (data.N k) rT x = q ∧
      rowBin (data.N k) rT (G k (data.γ k 1 s.i) (physCube (data.N k) B x)) = w} ≠ 0}.ncard : ℝ) ≤ H
  separation : ∀ c : ℤ, ENNReal.ofReal (16 * sourcePaletteBudget (data.K k) L H₀ H) *
    data.π k (data.γ k 1 s.i) (vel data k β c) ≤ 1
  base_ceiling : ∀ q : Fin 2 → ℤ, (data.ρ k (data.γ k 1 s.i)).restrict r.S₀
    {x | (fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k s.i) x e /
      data.N k ^ (-10 : ℝ)⌋ : ℤ)) = q} ≤
    ENNReal.ofReal ((100000 * data.K k ^ 7 * packetLength data k) * data.N k ^ (-20 : ℝ)) *
      data.ν k (data.γ k 1 s.i) (data.A k 1 s.i)

/-- Build exactly the finite Cartesian input, preserving the original laws and the full prior mass. -/
noncomputable def sourceCore {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H H₀ : ℝ}
    (s : SourcePacket data k M G E B ε L H) {Band : Set ℝ}
    (r : SourceRefinement s H₀ Band) {Λ β rT : ℝ} (θ : Measure Trajectory)
    (u : SourceCoreInput s r Λ β rT θ) : CorePacket M := by
  let ρ := data.ρ k (data.γ k 1 s.i)
  let ν := data.ν k (data.γ k 1 s.i)
  let h := packetLength data k
  let a := blockLeft (data.T k 1) (data.j k 1 s.i)
  have hNp : 0 < data.N k := by linarith [u.hN]
  have hΛp : 0 < Λ := by linarith [u.hΛ]
  have hH : 0 < H := by linarith [u.hH]
  have hK := s.original.budget_one
  have hKp : 0 < data.K k := by linarith
  have hh := s.original.positive_horizon
  have hK₇ : 1 ≤ data.K k ^ 7 := one_le_pow₀ hK
  have hD : 16 * H ≤ Λ := by
    have hle : 16 * H ≤ 1600000 * data.K k ^ 7 * H := by nlinarith
    exact hle.trans u.budget.relative_base
  have hbudget₀ : ENNReal.ofReal h * ν (data.A k 1 s.i) ≤ ENNReal.ofReal (16 * H) * ρ r.S₀ := by
    have hx := original_budget_of_mass_floor (by positivity : 0 < 1 / (16 * H)) r.mass_floor
    simpa only [one_div, inv_inv] using hx
  have hbudget : ENNReal.ofReal h * ν (boundedAssignment data k s.i (data.K k)) ≤
      ENNReal.ofReal Λ * ρ r.S₀ := by
    rw [boundedAssignment_mass s.original le_rfl]
    exact hbudget₀.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hD) le_rfl)
  have hmass : 0 < ρ r.S₀ := by
    have hprior : 0 < ν (data.A k 1 s.i) :=
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < data.N k ^ (-data.d) * h / data.K k)).trans_le
        s.original.prior_lower
    have hP : 0 < ENNReal.ofReal (1 / (16 * H)) * (ENNReal.ofReal h * ν (data.A k 1 s.i)) := by
      apply ENNReal.mul_pos
      · exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < 1 / (16 * H))).ne'
      · exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hh).ne' hprior.ne').ne'
    exact hP.trans_le r.mass_floor
  have horigin : (![a, originalOrigin data k s.i 1] : Fin 2 → ℝ) = originalOrigin data k s.i := by
    funext e
    fin_cases e <;> rfl
  have htime : I data (data.T k 1) (data.j k 1 s.i) = Icc a (a + h) := by
    rw [I_eq_blockInterval]
    rfl
  have hpalleq : sourcePaletteBudget (data.K k) L H₀ H =
      256000 * data.K k ^ 2 * L ^ 3 * H₀ ^ 4 * H := by
    dsimp [sourcePaletteBudget, fineCellBudget]
    ring
  have hpal : sourcePaletteBudget (data.K k) L H₀ H ≤ Λ := hpalleq.trans_le u.budget.palette
  have hLone : 1 ≤ L := by linarith [u.geometry_base]
  have hpalpos : 0 ≤ sourcePaletteBudget (data.K k) L H₀ H := by
    rw [hpalleq]
    positivity
  letI := s.original.probability_ν
  refine {
    N := data.N k, Λ := Λ, h := h, a := a, y₀ := originalOrigin data k s.i 1
    εT := fieldError (data.N k) h, rT := rT, B := B, L := 40
    ξ := data.N k ^ (-10 : ℝ), δv := data.N k ^ (-20 : ℝ), δs := data.N k ^ (-β)
    ρ := ρ, θ := θ, ν := ν, π := data.π k (data.γ k 1 s.i)
    E := E k (data.γ k 1 s.i), S₀ := r.S₀, A := boundedAssignment data k s.i (data.K k)
    G := G k (data.γ k 1 s.i)
    hN := u.hN, hΛ := u.hΛ, hh := hh, hh_one := s.original.bounded_horizon
    ha := blockLeft_nonneg _ _, ha_one := blockRight_le_one _ _, hεT := u.error_eq
    hξ := Real.rpow_pos_of_pos hNp _, hδv := Real.rpow_pos_of_pos hNp _, hδs := Real.rpow_pos_of_pos hNp _
    fit_precision := u.precision.fit, graph_precision := u.precision.graph
    layer_precision := u.precision.layer, base_precision := u.precision.base
    velocity_precision := u.precision.velocity, fine_precision := u.precision.fine
    separation_budget := ?_, separation_small := ?_
    finite_ρ := u.finite_ρ, finite_θ := u.finite_θ, sigma_ν := inferInstance
    probability_π := s.original.probability_π, measurable_E := u.measurable_E
    measurable_S₀ := r.measurable_S₀, measurable_A := measurableSet_boundedAssignment s.original _
    subset_E := fun x hx => s.subset_E (r.subset_source hx)
    subset_packet := ?_, positive_mass := hmass, original_density := ?_, original_mass := hbudget
    lower_graph_density := ?_, upper_graph_density := ?_
    coefficient_bound := ?_, base_bound := ?_, hidden_layer := ?_, graph_bound := ?_, coarse_lists := ?_
    separation := ?_, palette := ?_, qualified := ?_, base_ceiling := ?_ }
  · rw [Real.rpow_neg hNp.le]
    change 1 ≤ Λ / data.N k ^ β
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hNp β)).mpr (by simpa only [one_mul] using u.separation_budget)
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [u.hN]) (by linarith [u.hβ])
  · intro x hx
    have hp := s.subset_packet (r.subset_source hx)
    exact ⟨⟨hp.1, s.coefficients x (r.subset_source hx)⟩, htime ▸ hp.2⟩
  · apply (Measure.restrict_le_self.trans s.original.original_density).trans
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal u.budget.original) le_rfl
  · apply u.lower_graph_density.trans
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal u.budget.reference) le_rfl
  · apply u.upper_graph_density.trans
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal u.budget.reference) le_rfl
  · exact fun l hl e => (hl.2 e).trans u.budget.original
  · intro l hl t ht
    exact s.original.base_strip (u.geometry_base.trans u.budget.layer) l hl.1 t (htime.symm ▸ ht)
  · intro l hl l' hl' t ht t' ht'
    exact s.original.hidden_layer hNp (u.geometry_layer.trans u.budget.layer)
      l hl.1 l' hl'.1 t (htime.symm ▸ ht) t' (htime.symm ▸ ht')
  · intro x hx
    obtain ⟨hb, he⟩ := u.graph_bound x hx
    exact ⟨fun e => (hb e).trans u.budget.graph,
      he.trans (mul_le_mul_of_nonneg_right u.budget.graph (Real.rpow_nonneg hNp.le _))⟩
  · exact fun q => (u.coarse_lists q).trans u.budget.graph
  · intro q c
    exact separation_from_original_palette hpalpos (r.palette β u.band_separation q c) (u.separation c)
  · intro q c
    exact (r.palette 20 u.band_velocity q c).trans
      (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hpal) le_rfl) le_rfl)
  · intro x hx
    exact core_qualification_of_fit data k M G E B ε x s.i hNp hΛp u.qualification_budget
      (s.qualified x (r.subset_source hx))
  · intro q
    have hξsq : (data.N k ^ (-10 : ℝ)) ^ 2 = data.N k ^ (-20 : ℝ) := by
      rw [← Real.rpow_mul_natCast hNp.le]
      norm_num
    have hcap := u.base_ceiling q
    rw [← hξsq] at hcap
    have hrelative := cap_from_original_prior (by positivity : 0 ≤ 100000 * data.K k ^ 7)
      (by positivity : 0 ≤ 16 * H) hh.le
      (by nlinarith [u.budget.relative_base] : (100000 * data.K k ^ 7) * (16 * H) ≤ Λ) hcap hbudget₀
    simpa only [horigin, _root_.funext_iff] using hrelative

end Submission.Obl.k4_scalar_grid_cartesian_field
