/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, CoefficientCount.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupCaps
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.CoefficientSample
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.LabelDiameter
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! The horizontal coefficient count (paper Lemma `a06:horizontal-coefficient-count`)
for the original frozen residual law: on all but a power-small part of the
residual, the group, the time subbin and the hidden bin determine the full-time
hidden coefficient bin up to `N^ε` choices. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_coefficient_clustering

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The fitted assignments at a fixed depth are eventually measurable. -/
theorem Valid.eventually_B_measurable (h : cfg.Valid) {s : ℝ} (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i, MeasurableSet (cfg.B k s i) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]; linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.atlas R hR] with k hk
  exact fun i => ((hk s hRs hsU).2.2.1 i).2.1

/-- The global horizontal coefficient count at true depth `s`. -/
theorem Valid.eventually_coefficient_lists (h : cfg.Valid) {s : ℝ} (hs : 0 < s)
    (hsU : s ≤ cfg.U) (hse : s < cfg.e₀) (hs1 : s < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ k in atTop, ∃ (G : Set (α × ℝ))
      (CL : ℤ × ℤ × ℤ → ℤ → ℤ → Finset (Fin 3 → ℤ)),
      MeasurableSet G ∧ G ⊆ cfg.goodSet k s ∧
      cfg.ρ k (cfg.goodSet k s \ G) ≤ ENNReal.ofReal (cfg.N k ^ (-θ)) ∧
      (∀ g τ j, ((CL g τ j).card : ℝ) ≤ cfg.N k ^ ε) ∧
      ∀ p ∈ G, coefficientCode (cfg.N k ^ (-s)) (cfg.hiddenCoeff k p.1) ∈
        CL (cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1)
          ⌊p.2 / cfg.N k ^ (-(2 * s))⌋ ⌊cfg.hidden k p / cfg.N k ^ (-s)⌋ := by
  obtain ⟨ηc, hηc, N₀, hN₀, hcl⟩ := scalar_weighted_heavy_coefficient_cover cfg.d s (ε / 4)
    h.dimension_nonneg h.dimension_lt_one hs (by positivity)
  set ε₁ := min (ηc / 4) (ε / 4) with hε₁def
  set θ₂ := min (ηc / 2) (ε / 4) with hθ₂def
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hθ₂ : 0 < θ₂ := lt_min (by positivity) (by positivity)
  have hε₁η : ε₁ ≤ ηc / 4 := min_le_left _ _
  have hε₁ε : ε₁ ≤ ε / 4 := min_le_right _ _
  have hθ₂η : θ₂ ≤ ηc / 2 := min_le_left _ _
  have hθ₂ε : θ₂ ≤ ε / 4 := min_le_right _ _
  refine ⟨θ₂ / 2, by positivity, ?_⟩
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => le_trans (by norm_num) (h.scale k)
  have hsub := h.subpower.2
  have hKge := h.subpower.1
  have e2 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt h.scale_limit
    (show -s < 0 by linarith) (11 / 4 : ℝ)
  have e3 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 1 (show -(2 * s) < -s by linarith) (show (0 : ℝ) ≤ 9 by norm_num)
  have e5 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 1 (show (0 : ℝ) < ηc from hηc) (show (0 : ℝ) ≤ 3 by norm_num)
  have e6 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 1 (show ε₁ < ηc by linarith) (show (0 : ℝ) ≤ 12 by norm_num)
  have e7 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 0 (show ε₁ < ηc by linarith) (show (0 : ℝ) ≤ 8 by norm_num)
  have e8 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 0 (show ε₁ + ε / 4 + θ₂ < ε by linarith)
    (show (0 : ℝ) ≤ 22 by norm_num)
  have e9a := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 1 (show ε₁ - ηc < -(θ₂ / 2) by linarith)
    (show (0 : ℝ) ≤ 36 by norm_num)
  have e9b := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 2 (show -ηc < -(θ₂ / 2) by linarith)
    (show (0 : ℝ) ≤ 75 by norm_num)
  have e9c := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit hKge hsub 1 (show -θ₂ < -(θ₂ / 2) by linarith)
    (show (0 : ℝ) ≤ 6 by norm_num)
  have eN₀ : ∀ᶠ k in atTop, N₀ ≤ cfg.N k := h.scale_limit.eventually (eventually_ge_atTop N₀)
  filter_upwards [h.eventually_group_band_cap hs hse hε₁,
    h.eventually_group_support hs hsU hse hε₁, h.eventually_B_measurable hs hsU,
    e2, e3, e5, e6, e7, e8, e9a, e9b, e9c, eN₀] with k hB hS hBm h2 h3 h5 h6 h7 h8 h9a h9b h9c hN₀k
  have hNpos : 0 < cfg.N k := by linarith [h.scale k]
  have hN1k : 1 < cfg.N k := by linarith [h.scale k]
  haveI := (h.basic k).2.1
  haveI := (h.basic k).2.2.1
  haveI := h.residual_finite k
  have hρμ := (h.basic k).2.2.2.2.1
  have hdom := (h.basic k).2.2.2.1
  simp only [Real.rpow_zero, pow_one, pow_zero, mul_one] at h2 h3 h5 h6 h7 h8 h9a h9b h9c
  have hρtot : cfg.ρ k (cfg.goodSet k s) ≤ ENNReal.ofReal (cfg.K k) :=
    (measure_mono (subset_univ _)).trans ((hρμ _).trans (h.incidence_mass_le k))
  obtain ⟨G, CL, hGm, hGsub, hloss, hcard, hmem⟩ := cfg.coefficient_lists_at_sample k
    (h.basic k).1 hBm hρμ hdom (hKge k) hN1k hs h.dimension_nonneg h.dimension_lt_one
    hθ₂.le (by positivity : (0 : ℝ) ≤ ε / 4) hB hS (hcl (cfg.N k) hN₀k α) (by linarith)
    h3.le (Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)) h5.le h6.le h7.le hρtot
  refine ⟨G, CL, hGm, hGsub, hloss.trans (ENNReal.ofReal_le_ofReal ?_), fun g τ j =>
    (hcard g τ j).trans h8.le, hmem⟩
  have hsplit : 12 * cfg.K k * cfg.N k ^ ε₁ / cfg.N k ^ ηc =
      12 * cfg.K k * cfg.N k ^ (ε₁ - ηc) := by
    rw [Real.rpow_sub hNpos]; ring
  rw [hsplit]
  linarith

/-- The label inputs of the diameter argument, from one fitted incidence of the label. -/
theorem AssignmentLevel.labelDiameterInputs (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (lev : cfg.AssignmentLevel k s) (hs : 0 < s) (i : Fin (cfg.n k s))
    (l₀ : α) (hl₀ : l₀ ∈ cfg.B k s i) (t₀ : ℝ) (ht₀ : t₀ ∈ I (cfg.T k s) (cfg.j k s i)) :
    ∃ L : Fin 4 → ℝ, cfg.LabelDiameterInputs k s i L := by
  obtain ⟨L, -, hslopes, hfit⟩ := lev.active_affine_entry h hs.le i l₀ hl₀ t₀ ht₀
  have hNpos : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hcmp := time_length_comparison hNpos hK lev.time_lower lev.time_upper
  have hq : cfg.timeLength k s ≤ cfg.K k * cfg.N k ^ (-cfg.κ * s) := by
    have := hcmp.1
    unfold timeLength
    rwa [div_le_iff₀ hK, mul_comm] at this
  have hqg : cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * cfg.N k ^ (-s) := by
    rw [h.horizontal_rate]
    calc
      cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s) ≤
          cfg.K k * cfg.N k ^ (-cfg.κ * s) * cfg.N k ^ (-cfg.κ * s) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hNpos.le _)
      _ = cfg.K k * cfg.N k ^ (-s) := by
        have hexp : -cfg.κ * s + -cfg.κ * s = -s := by linear_combination (-s) * h.critical_rate
        rw [mul_assoc, ← Real.rpow_add hNpos, hexp]
  refine ⟨L, ⟨lev.coefficient_bound i, ?_, hslopes, ?_⟩⟩
  · intro l hl t ht
    have hg := (lev.geometry i l (lev.fitted_subset i hl) t ht).2.1
    simp only [x, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hg
    refine hg.trans ?_
    calc
      cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) =
          cfg.K k * (cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s)) := by ring
      _ ≤ cfg.K k * (cfg.K k * cfg.N k ^ (-s)) := mul_le_mul_of_nonneg_left hqg hK.le
      _ = cfg.K k ^ 2 * cfg.N k ^ (-s) := by ring
  · intro l hl t ht
    have hf := hfit l hl t ht
    have heq : affineResidualIntercept L (cfg.b k l) + t * affineResidualSlope L (cfg.b k l) =
        (cfg.b k l 2 + t * cfg.b k l 5) - (L 0 + L 1 * t + L 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L 3 * (cfg.b k l 1 + t * cfg.b k l 4)) := by
      simp only [affineResidualIntercept, affineResidualSlope]; ring
    rwa [heq] at hf

/-- Derivative lists in every true label at depth `s`, indexed by the
normalized base cell and the velocity bin at any mesh `N^(-xe)`, `xe ≥ 2s`. -/
theorem Valid.eventually_label_derivative_lists (h : cfg.Valid) {s xe : ℝ} (hs : 0 < s)
    (hsU : s ≤ cfg.U) (hse : s < cfg.e₀) (hs1 : s < 1) (hxe : 2 * s ≤ xe)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ k in atTop, ∃ (G : Set (α × ℝ))
      (Λ : Fin (cfg.n k s) → (Fin 2 → ℤ) → ℤ → Finset ℤ),
      MeasurableSet G ∧ G ⊆ cfg.goodSet k s ∧
      cfg.ρ k (cfg.goodSet k s \ G) ≤ ENNReal.ofReal (cfg.N k ^ (-θ)) ∧
      (∀ i c z, ((Λ i c z).card : ℝ) ≤ cfg.N k ^ ε) ∧
      ∀ i, ∀ p ∈ G, p.1 ∈ cfg.B k s i → p.2 ∈ I (cfg.T k s) (cfg.j k s i) →
        ⌊cfg.b k p.1 5 / cfg.N k ^ (-s)⌋ ∈
          Λ i (cfg.labelCell k s (cfg.N k ^ (-xe)) i p) ⌊cfg.b k p.1 3 / cfg.N k ^ (-xe)⌋ := by
  classical
  obtain ⟨θ, hθ, hev⟩ := h.eventually_coefficient_lists hs hsU hse hs1
    (show 0 < ε / 2 by positivity)
  refine ⟨θ, hθ, ?_⟩
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => le_trans (by norm_num) (h.scale k)
  have ecard := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 30 (show ε / 2 < ε by linarith)
    (show (0 : ℝ) ≤ 131 ^ 5 by norm_num)
  have eξ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 1 (show -xe < -s by linarith)
    (show (0 : ℝ) ≤ 3 by norm_num)
  filter_upwards [hev, h.eventually_assignment_level hs hsU, ecard, eξ] with k hk lev hcard hξa
  obtain ⟨G, CL, hGm, hGsub, hloss, hCLcard, hmem⟩ := hk
  simp only [pow_one] at hξa
  have hK := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hNpos : 0 < cfg.N k := by linarith [h.scale k]
  have hN1k : 1 < cfg.N k := by linarith [h.scale k]
  set a := cfg.N k ^ (-s) with hadef
  set δ := cfg.N k ^ (-(2 * s)) with hδdef
  set ξ := cfg.N k ^ (-xe) with hξdef
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNpos _
  have hξδ : ξ ≤ δ := Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  have he₀ : cfg.N k ^ (-cfg.e₀) ≤ a := Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  let tuple : α × ℝ → (ℤ × ℤ × ℤ) × ℤ × ℤ := fun p =>
    (cfg.groupCode k a δ p.1, ⌊p.2 / δ⌋, ⌊cfg.hidden k p / a⌋)
  set R : ℤ := ⌈60 * cfg.K k ^ 6 + 4⌉ with hRdef
  let box : (ℤ × ℤ × ℤ) × ℤ × ℤ → Finset ((ℤ × ℤ × ℤ) × ℤ × ℤ) := fun c =>
    (Finset.Icc (c.1.1 - R) (c.1.1 + R) ×ˢ (Finset.Icc (c.1.2.1 - R) (c.1.2.1 + R) ×ˢ
      Finset.Icc (c.1.2.2 - R) (c.1.2.2 + R))) ×ˢ
    (Finset.Icc (c.2.1 - R) (c.2.1 + R) ×ˢ Finset.Icc (c.2.2 - R) (c.2.2 + R))
  let Λ : Fin (cfg.n k s) → (Fin 2 → ℤ) → ℤ → Finset ℤ := fun i c z =>
    if hex : ∃ p, p ∈ G ∧ p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        cfg.labelCell k s ξ i p = c ∧ ⌊cfg.b k p.1 3 / ξ⌋ = z then
      ((box (tuple (Classical.choose hex))).biUnion (fun tr => CL tr.1 tr.2.1 tr.2.2)).image
        (fun q => q 1)
    else ∅
  have hR0 : (0 : ℤ) ≤ R := Int.ceil_nonneg (by positivity)
  have hRle : (R : ℝ) ≤ 60 * cfg.K k ^ 6 + 5 := by
    have := Int.ceil_lt_add_one (60 * cfg.K k ^ 6 + 4); linarith
  have hIcc : ∀ x : ℤ, ((Finset.Icc (x - R) (x + R)).card : ℝ) = 2 * R + 1 := by
    intro x
    rw [Int.card_Icc]
    have hnat : (((x + R + 1 - (x - R)).toNat : ℕ) : ℤ) = 2 * R + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    exact_mod_cast hnat
  have hbox : ∀ c, ((box c).card : ℝ) ≤ 131 ^ 5 * cfg.K k ^ 30 := by
    intro c
    simp only [box, Finset.card_product]
    push_cast
    rw [hIcc, hIcc, hIcc, hIcc, hIcc]
    have h2R : 2 * (R : ℝ) + 1 ≤ 131 * cfg.K k ^ 6 := by
      have : 1 ≤ cfg.K k ^ 6 := one_le_pow₀ hK
      linarith
    have hR0' : (0 : ℝ) ≤ R := by exact_mod_cast hR0
    have h2R0 : 0 ≤ 2 * (R : ℝ) + 1 := by linarith
    calc
      (2 * (R : ℝ) + 1) * ((2 * R + 1) * (2 * R + 1)) * ((2 * R + 1) * (2 * R + 1)) =
          (2 * (R : ℝ) + 1) ^ 5 := by ring
      _ ≤ (131 * cfg.K k ^ 6) ^ 5 := pow_le_pow_left₀ h2R0 h2R 5
      _ = 131 ^ 5 * cfg.K k ^ 30 := by ring
  refine ⟨G, Λ, hGm, hGsub, hloss, ?_, ?_⟩
  · intro i c z
    simp only [Λ]
    split_ifs with hex
    · have h1 : (((box (tuple (Classical.choose hex))).biUnion
            (fun tr => CL tr.1 tr.2.1 tr.2.2)).image (fun q => q 1)).card ≤
            ∑ tr ∈ box (tuple (Classical.choose hex)), (CL tr.1 tr.2.1 tr.2.2).card :=
          Finset.card_image_le.trans Finset.card_biUnion_le
      calc
        ((((box (tuple (Classical.choose hex))).biUnion
            (fun tr => CL tr.1 tr.2.1 tr.2.2)).image (fun q => q 1)).card : ℝ) ≤
            ((∑ tr ∈ box (tuple (Classical.choose hex)), (CL tr.1 tr.2.1 tr.2.2).card : ℕ) : ℝ) := by
          exact_mod_cast h1
        _ = ∑ tr ∈ box (tuple (Classical.choose hex)), ((CL tr.1 tr.2.1 tr.2.2).card : ℝ) := by
          push_cast; rfl
        _ ≤ ∑ _tr ∈ box (tuple (Classical.choose hex)), cfg.N k ^ (ε / 2) :=
          Finset.sum_le_sum (fun tr _ => hCLcard _ _ _)
        _ = ((box (tuple (Classical.choose hex))).card : ℝ) * cfg.N k ^ (ε / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 131 ^ 5 * cfg.K k ^ 30 * cfg.N k ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right (hbox _) (Real.rpow_nonneg hNpos.le _)
        _ ≤ cfg.N k ^ ε := hcard.le
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  · intro i p hpG hpB hpI
    have hex : ∃ p', p' ∈ G ∧ p'.1 ∈ cfg.B k s i ∧ p'.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        cfg.labelCell k s ξ i p' = cfg.labelCell k s ξ i p ∧
        ⌊cfg.b k p'.1 3 / ξ⌋ = ⌊cfg.b k p.1 3 / ξ⌋ := ⟨p, hpG, hpB, hpI, rfl, rfl⟩
    simp only [Λ, hex, dite_true]
    obtain ⟨hp₀G, hp₀B, hp₀I, hp₀cell, hp₀v⟩ := Classical.choose_spec hex
    set p₀ := Classical.choose hex
    obtain ⟨L, hin⟩ := lev.labelDiameterInputs h hs i p.1 hpB p.2 hpI
    have hclose := cfg.label_tuple_close k i L hin hK hN1k hs hξ hξδ hξa.le he₀
      (hGsub hp₀G) (hGsub hpG) ⟨hp₀B, hp₀I⟩ ⟨hpB, hpI⟩ hp₀cell hp₀v
    obtain ⟨c0, c1, c3, ct, cw⟩ := hclose
    have hmemR : ∀ (u v : ℤ), |((u - v : ℤ) : ℝ)| ≤ 60 * cfg.K k ^ 6 + 4 →
        v ∈ Finset.Icc (u - R) (u + R) := by
      intro u v huv
      have hR' : 60 * cfg.K k ^ 6 + 4 ≤ (R : ℝ) := Int.le_ceil _
      have h1 := abs_le.mp (huv.trans hR')
      have h1a : ((u - v : ℤ) : ℝ) ≤ R := h1.2
      have h1b : -(R : ℝ) ≤ ((u - v : ℤ) : ℝ) := h1.1
      have h2a : u - v ≤ R := by exact_mod_cast h1a
      have h2b : -R ≤ u - v := by exact_mod_cast h1b
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine Finset.mem_image.mpr ⟨coefficientCode a (cfg.hiddenCoeff k p.1), ?_, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨tuple p, ?_, hmem p hpG⟩
    simp only [box, tuple, Finset.mem_product, groupCode]
    exact ⟨⟨hmemR _ _ c0, hmemR _ _ c1, hmemR _ _ c3⟩, hmemR _ _ ct, hmemR _ _ cw⟩

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
