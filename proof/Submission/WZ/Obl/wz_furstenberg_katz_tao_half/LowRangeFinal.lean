-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.LowRangeFinal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.LowRange
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers

/-!
# The Furstenberg bush estimate in the low range `σ ≤ 1/2 - c`

The literal statement of the Furstenberg child (o157) restricted to
`1/4 ≤ σ ≤ 1/2 - c`, proved by Wolff's bush argument (`low_range_core`) with
`η = c/26`, `ε₀ = c/2`, `ρ₀ = r ^ (8 η) / 256`, `λ = 33 r / ρ₀`.

Ported from session x0394 (o141, commit d684c60).  The only lemma it used from the
single-scale machinery there, `exists_rpow_le`, is replaced by the identical accepted
lemma `WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

lemma rpow_quarter_256 : (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
  rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem furstenberg_low_range : ∀ c : ℝ, 0 < c → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 / 2 - c → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ) := by
  intro c hc
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (c / 26) (1 / 104) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min (by positivity) (by norm_num)
  have hη104 : η ≤ 1 / 104 := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨r₁, hr₁, hr₁spec⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := 1 - 8 * η) (B := 1 / 256) (by linarith) (by norm_num)
  obtain ⟨r₂, hr₂, hr₂spec⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := c / 2) (B := 1 / 67584) (by positivity) (by norm_num)
  refine ⟨c / 2, η, min (min r₁ r₂) 1, by positivity, hη, by positivity, ?_⟩
  intro r σ hr hrr₀ hσ1 hσ2 P D hPfin hPne hDfin hP4 hPfr hDmem hbush hsep hKT
  have hc4 : c ≤ 1 / 4 := by linarith
  have hηc : η = c / 26 := by rw [hηdef]; exact min_eq_left (by linarith)
  have hr1 : r ≤ r₁ := hrr₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : r ≤ r₂ := hrr₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrle1 : r ≤ 1 := hrr₀.trans (min_le_right _ _)
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : ℝ, ρ₀ = r ^ (8 * η) / 256 := ⟨_, rfl⟩
  have hr8 : 0 < r ^ (8 * η) := Real.rpow_pos_of_pos hr _
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; positivity
  have hρ₀1 : ρ₀ ≤ 1 := by
    rw [hρ₀def]
    have : r ^ (8 * η) ≤ 1 := Real.rpow_le_one hr.le hrle1 (by positivity)
    linarith
  have hρ₀r : r ≤ ρ₀ := by
    have h1 := hr₁spec r hr hr1
    have h2 : r = r ^ (1 - 8 * η) * r ^ (8 * η) := by
      rw [← Real.rpow_add hr]; norm_num
    rw [hρ₀def, h2]
    have : r ^ (1 - 8 * η) * r ^ (8 * η) ≤ 1 / 256 * r ^ (8 * η) :=
      mul_le_mul_of_nonneg_right h1 hr8.le
    have h3 : r ^ (1 - 8 * η + 8 * η) = r ^ (1 - 8 * η) * r ^ (8 * η) := Real.rpow_add hr _ _
    rw [← h2] at this ⊢
    linarith
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = 33 * r / ρ₀ := ⟨_, rfl⟩
  have hfar : 2 * r ^ (-η) * (ρ₀ / r) ^ σ ≤ r ^ (η - σ) / 2 := by
    have h1 : ρ₀ ^ σ ≤ ρ₀ ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hρ₀pos hρ₀1 hσ1
    have h2 : ρ₀ ^ (1 / 4 : ℝ) = r ^ (2 * η) / 4 := by
      rw [hρ₀def, Real.div_rpow hr8.le (by norm_num), ← Real.rpow_mul hr.le, rpow_quarter_256]
      congr 2; ring
    have h3 : (ρ₀ / r) ^ σ = ρ₀ ^ σ / r ^ σ := Real.div_rpow hρ₀pos.le hr.le σ
    have h4 : r ^ (-η) * r ^ (2 * η) = r ^ η := by rw [← Real.rpow_add hr]; congr 1; ring
    have h5 : r ^ (η - σ) = r ^ η / r ^ σ := Real.rpow_sub hr η σ
    have hrσ : 0 < r ^ σ := Real.rpow_pos_of_pos hr σ
    have hrη : 0 < r ^ (-η) := Real.rpow_pos_of_pos hr _
    rw [h3, h5]
    calc 2 * r ^ (-η) * (ρ₀ ^ σ / r ^ σ) ≤ 2 * r ^ (-η) * ((r ^ (2 * η) / 4) / r ^ σ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (h1.trans h2.le) hrσ.le
      _ = (r ^ (-η) * r ^ (2 * η)) / (2 * r ^ σ) := by ring
      _ = r ^ η / r ^ σ / 2 := by rw [h4]; ring
  obtain ⟨J, hJD, hJsep, hJW⟩ := low_range_core (lam := lam) (KT := r ^ (-η)) (F := r ^ (-η))
    (Nb := r ^ (η - σ)) hr (by linarith) hρ₀r hρ₀1 (by rw [hlamdef])
    (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hr _) hfar
    P D hPfin hPne hDfin hP4 hPfr hDmem hbush hKT
  refine ⟨J, hJD, hJsep, ?_⟩
  -- the numerics
  have hlam : lam = 8448 * r ^ (1 - 8 * η) := by
    rw [hlamdef, hρ₀def, Real.rpow_sub hr, Real.rpow_one]; field_simp; ring
  have hden : 8 * (r ^ (-η)) ^ 2 * r ^ (-η) * lam = 67584 * r ^ (1 - 11 * η) := by
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have : r ^ ((-η) * ((2 : ℕ) : ℝ)) * r ^ (-η) * r ^ (1 - 8 * η) = r ^ (1 - 11 * η) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr]; congr 1; push_cast; ring
    calc 8 * r ^ ((-η) * ((2 : ℕ) : ℝ)) * r ^ (-η) * (8448 * r ^ (1 - 8 * η))
        = 67584 * (r ^ ((-η) * ((2 : ℕ) : ℝ)) * r ^ (-η) * r ^ (1 - 8 * η)) := by ring
      _ = 67584 * r ^ (1 - 11 * η) := by rw [this]
  have hnum : (r ^ (η - σ)) ^ 2 = r ^ (2 * η - 2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have hX : (r ^ (-(2 * σ) - c / 2)) ^ 2 = r ^ (-4 * σ - c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have hexp : 13 * η + 2 * σ - 1 + c ≤ -(c / 2) := by rw [hηc]; linarith
  have hbig : 67584 ≤ r ^ (13 * η + 2 * σ - 1 + c) := by
    have h1 : r ^ (-(c / 2)) ≤ r ^ (13 * η + 2 * σ - 1 + c) :=
      Real.rpow_le_rpow_of_exponent_ge hr hrle1 hexp
    have h2 := hr₂spec r hr hr2
    have h3 : r ^ (-(c / 2)) = (r ^ (c / 2))⁻¹ := Real.rpow_neg hr.le _
    have h4 : (67584 : ℝ) ≤ (r ^ (c / 2))⁻¹ := by
      have hp : 0 < r ^ (c / 2) := Real.rpow_pos_of_pos hr _
      rw [le_inv_comm₀ (by norm_num) hp]
      calc r ^ (c / 2) ≤ 1 / 67584 := h2
        _ = 67584⁻¹ := by norm_num
    linarith
  have key : (r ^ (-(2 * σ) - c / 2)) ^ 2 ≤
      (r ^ (η - σ)) ^ 2 / (8 * (r ^ (-η)) ^ 2 * r ^ (-η) * lam) := by
    rw [hX, hden, hnum, le_div_iff₀ (by positivity)]
    have hsplit : r ^ (2 * η - 2 * σ) =
        (r ^ (-4 * σ - c) * r ^ (1 - 11 * η)) * r ^ (13 * η + 2 * σ - 1 + c) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr]; congr 1; ring
    rw [hsplit]
    have hp : 0 < r ^ (-4 * σ - c) * r ^ (1 - 11 * η) := by positivity
    nlinarith
  have hfinal := key.trans hJW
  have hX0 : 0 ≤ r ^ (-(2 * σ) - c / 2) := Real.rpow_nonneg hr.le _
  exact (pow_le_pow_iff_left₀ hX0 (Nat.cast_nonneg _) two_ne_zero).mp hfinal

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
