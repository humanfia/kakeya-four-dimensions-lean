import Mathlib
import ChallengeDeps
import Submission.Obl.k4_horizontal_three_traversal_spreading.Quantitative
import Submission.Obl.k4_horizontal_three_traversal_spreading.Scales
set_option linter.unusedVariables false

/-!
# `Submission.k4_horizontal_three_traversal_spreading`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_horizontal_three_traversal_spreading`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_horizontal_three_traversal_spreading/`
belong to this obligation.
-/

theorem Submission.k4_horizontal_three_traversal_spreading : ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (σ : MeasureTheory.Measure (α × ℝ)) (π : MeasureTheory.Measure ℝ) (x : α → ℝ → Fin 3 → ℝ) (vel : α → ℝ) (bin : α → ℤ) (state : α × ℝ → ℕ) (G : Set (α × ℝ)), (MeasureTheory.IsProbabilityMeasure σ ∧ MeasureTheory.IsProbabilityMeasure π ∧ Measurable (Function.uncurry x) ∧ Measurable vel ∧ Measurable bin ∧ Measurable state ∧ MeasurableSet G ∧ σ Gᶜ = 0 ∧ σ ≤ ENNReal.ofReal (N ^ δ) • ((σ.map Prod.fst).prod MeasureTheory.volume) ∧ (∀ p ∈ G, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |vel p.1| ≤ N ^ δ ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, x p.1 t 0 = t ∧ ∀ e, |x p.1 t e| ≤ N ^ δ) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1, x p.1 u 1 = x p.1 t 1 + vel p.1 * (u - t) ∧ |x p.1 u 2 - x p.1 t 2 - (-x p.1 t 1 + t * vel p.1) * (u - t)| ≤ N ^ (-20 * a)) ∧ (∀ p ∈ G, ∀ q ∈ G, state p = state q → bin p.1 = bin q.1 ∧ ∀ e, |x p.1 p.2 e - x q.1 q.2 e| ≤ N ^ (-20 * a)) ∧ (∀ (q : ℕ) (j : ℤ), σ {p | state p = q ∧ ⌊vel p.1 / N ^ (-20 * a)⌋ = j} ≤ ENNReal.ofReal (N ^ δ) * σ {p | state p = q} * π {w | ⌊w / N ^ (-20 * a)⌋ = j}) ∧ (∀ z r : ℝ, N ^ (-20 * a) ≤ r → r ≤ 1 → π (Set.Icc (z - r) (z + r)) ≤ ENNReal.ofReal (N ^ δ * r ^ S))) → ∀ F : Finset (ℤ × (Fin 3 → ℤ)), (∀ᵐ p ∂σ, (bin p.1, fun e => ⌊x p.1 p.2 e / N ^ (-a)⌋) ∈ F) → ∃ j : ℤ, ENNReal.ofReal (N ^ (-ε) / ((F.card : ℝ) * (N ^ (-a)) ^ 3)) ≤ σ {p | bin p.1 = j} := by
  classical
  obtain ⟨C, hC, hspread⟩ := Submission.Obl.k4_horizontal_three_traversal_spreading.quantitative_spreading
  intro S a ε hS ha hε
  obtain ⟨δ, hδ, hδε, κ, hκ, N₀, hN₀, hscales⟩ :=
    Submission.Obl.k4_horizontal_three_traversal_spreading.choose_scales C S a ε hS ha hε
  refine ⟨δ, hδ, hδε, N₀, hN₀, ?_⟩
  intro N hN α _ σ π x vel bin state G hdata F hF
  rcases hdata with ⟨hσ, hπ, hx, hvel, hbin, hstate, hG, hfull, hdensity, hgeometry,
    hstate_geometry, hpalette, hnonconc⟩
  letI := hσ
  letI := hπ
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < N ^ κ := Real.rpow_pos_of_pos hN0 _
  obtain ⟨hK, hL, hB, hfine, hgeom, hloss, hcost⟩ := hscales N hN
  let D : Submission.Obl.k4_horizontal_three_traversal_spreading.Law α :=
    { σ := σ, π := π, x := x, vel := vel, bin := bin, state := state, G := G, F := F,
      h := N ^ (-20 * a), ω := N ^ (-a), L := N ^ δ, B := N ^ δ }
  have hD : D.Valid :=
    { prob_σ := hσ, prob_π := hπ, meas_x := hx, meas_vel := hvel,
      meas_bin := hbin, meas_state := hstate, meas_G := hG, full_G := hfull,
      density := hdensity, geometry := hgeometry, state_geometry := hstate_geometry,
      palette := hpalette, support := hF,
      h_pos := Real.rpow_pos_of_pos hN0 _, ω_pos := Real.rpow_pos_of_pos hN0 _,
      L_nonneg := Real.rpow_nonneg hN0.le _, B_nonneg := Real.rpow_nonneg hN0.le _ }
  have hpal : ∀ v : ℝ, π (Set.Icc (v - 2 / N ^ κ) (v + 2 / N ^ κ)) ≤
      ENNReal.ofReal (N ^ δ * (2 / N ^ κ) ^ S) := by
    intro v
    apply hnonconc v (2 / N ^ κ)
    · exact hfine.trans (by rw [div_eq_mul_inv (2 : ℝ) (N ^ κ)]; linarith [inv_pos.mpr hK0])
    · exact (div_le_one hK0).mpr hK
  obtain ⟨j, hj⟩ := hspread α D hD (N ^ κ) (N ^ δ * (2 / N ^ κ) ^ S)
    hK hL (by positivity) hB hfine hgeom hloss hpal
  have hFpos : 0 < (F.card : ℝ) := by
    obtain ⟨p, hp⟩ := hF.exists
    exact_mod_cast Finset.card_pos.mpr ⟨_, hp⟩
  have hCcost : 0 < C * (N ^ κ) ^ 24 * (N ^ δ) ^ 6 := by positivity
  have hprod := mul_le_mul_of_nonneg_right hcost
    (show 0 ≤ (F.card : ℝ) * (N ^ (-a)) ^ 3 by positivity)
  have hinv := one_div_le_one_div_of_le
    (show 0 < (C * (N ^ κ) ^ 24 * (N ^ δ) ^ 6) * ((F.card : ℝ) * (N ^ (-a)) ^ 3) by positivity)
    hprod
  have hsmall : N ^ (-ε) / ((F.card : ℝ) * (N ^ (-a)) ^ 3) ≤
      1 / (C * (N ^ κ) ^ 24 * (N ^ δ) ^ 6 * (F.card : ℝ) * (N ^ (-a)) ^ 3) := by
    simpa only [Real.rpow_neg hN0.le, inv_eq_one_div, div_div, mul_assoc] using hinv
  refine ⟨j, ?_⟩
  apply (ENNReal.ofReal_le_iff_le_toReal (MeasureTheory.measure_ne_top σ _)).mpr
  exact hsmall.trans hj
