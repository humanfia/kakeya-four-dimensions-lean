-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactPowerLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensRank
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.RankPowerLoss
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.DegreeLogLoss
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CoefficientPacking
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LocalizationParameters

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- The rank and degree losses together cost any prescribed positive
power of the resolution. The constant is uniform in the rank base once
that base has the stated lower growth. -/
theorem exists_contact_rank_degree_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B δ s l u : ℝ) (N : ℕ),
      1 < B → 4 ≤ B ^ (ε / 2) → 0 < δ → δ ≤ 1 → δ ≤ s →
      l ≤ u → u - l ≤ 1 → (N : ℝ) * δ ^ 6 ≤ 8192000000 →
      ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3) ≤ C * δ ^ (-ε) := by
  obtain ⟨C₀, hC₀, hdegree⟩ := exists_degree_log_loss (ε / 2) (by positivity)
    8192000000 (by norm_num)
  let C₁ : ℝ := max 1 C₀
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  refine ⟨17 * C₁, by positivity, ?_⟩
  intro B δ s l u N hB hbase hδ hδ1 hδs hlu hwidth hpack
  have hε2 : 0 ≤ ε / 2 := by positivity
  have hone : 1 ≤ δ ^ (-(ε / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hε2)
  have hrank : (4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1 ≤
      17 * δ ^ (-(ε / 2)) := by
    have hh := four_pow_resolution_rank_le hB hδ hδ1 hδs
      (sub_nonneg.mpr hlu) hwidth hε2 hbase
    simpa only [windowLensHeight, lensWidthRank, Nat.add_assoc] using hh
  have hlog : (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3) ≤ C₁ * δ ^ (-(ε / 2)) := by
    by_cases hN : N = 0
    · subst N
      simp only [Nat.log_zero_right, zero_add, Nat.cast_one, one_pow]
      exact le_trans hone (le_mul_of_one_le_left (by positivity) hC₁)
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      have hL1 : (1 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (Nat.log 2 N) (α := ℝ)]
      calc
        _ = ((Nat.log 2 N : ℝ) + 1) ^ 3 := by push_cast; rfl
        _ ≤ ((Nat.log 2 N : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
        _ ≤ C₀ * δ ^ (-(ε / 2)) := hdegree δ hδ N hN1 hpack
        _ ≤ C₁ * δ ^ (-(ε / 2)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc
    _ ≤ (17 * δ ^ (-(ε / 2))) * (C₁ * δ ^ (-(ε / 2))) :=
      mul_le_mul hrank hlog (by positivity) (by positivity)
    _ = (17 * C₁) * (δ ^ (-(ε / 2)) * δ ^ (-(ε / 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hδ]
      congr 2
      ring

/-- The coefficient refinement and all finite incidence losses may be
chosen simultaneously using only the exponent. -/
theorem exists_contact_loss_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ B θ C : ℝ, 1 < B ∧ 0 < θ ∧ θ ≤ 1 / 10000 ∧ 0 < C ∧
      (∀ D : ℝ, 0 ≤ D → 2 * (19 * (θ * D)) * B ≤ D / 120) ∧
      ∀ (δ s l u : ℝ) (N : ℕ), 0 < δ → δ ≤ 1 → δ ≤ s →
        l ≤ u → u - l ≤ 1 → (N : ℝ) * δ ^ 6 ≤ 8192000000 →
        ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) *
          (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3) ≤ C * δ ^ (-ε) := by
  obtain ⟨B, θ, hB, hbase, hθ, hθsmall, hratio⟩ :=
    exists_rank_refinement (ε / 2) (by positivity)
  obtain ⟨C, hC, hloss⟩ := exists_contact_rank_degree_loss ε hε
  exact ⟨B, θ, C, hB, hθ, hθsmall, hC, hratio,
    fun δ s l u N hδ hδ1 hδs hlu hwidth hpack =>
      hloss B δ s l u N hB hbase hδ hδ1 hδs hlu hwidth hpack⟩

/-- A finite pair of subfamilies in the frozen coefficient ball supplies
the polynomial packing premise needed by the uniform loss estimate. -/
theorem contact_rank_degree_loss_of_coefficient_packing
    {ε C B δ s l u : ℝ} {n : ℕ}
    (hloss : ∀ (δ s l u : ℝ) (N : ℕ), 0 < δ → δ ≤ 1 → δ ≤ s →
      l ≤ u → u - l ≤ 1 → (N : ℝ) * δ ^ 6 ≤ 8192000000 →
      ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3) ≤ C * δ ^ (-ε))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδs : δ ≤ s) (hlu : l ≤ u) (hwidth : u - l ≤ 1)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (hq : ∀ i, ‖q i‖ ≤ 10)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) (A F : Finset (Fin n)) :
    ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) *
      (((Nat.log 2 (A.card + F.card) + 1 : ℕ) : ℝ) ^ 3) ≤ C * δ ^ (-ε) := by
  apply hloss δ s l u (A.card + F.card) hδ hδ1 hδs hlu hwidth
  simpa only [Nat.cast_add] using
    coefficient_subfamilies_mass_mul_scale_six_le hδ hδ1 q hq hsep A F

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
