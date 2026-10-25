-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.AbstractTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_slab_error_removal.Interfaces
import Submission.WZ.Obl.wz_small_slab_error_removal.GeometricArithmetic

namespace WangZahlLot.Obl.wz_small_slab_error_removal.Model

set_option maxHeartbeats 800000

/-- A relative-scale version of the restricted estimate, using only the
abstract monotonicity and packing/averaging bounds. -/
theorem restricted_relative {P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop}
    {C s w : ℝ} (hC : 1 ≤ C) (hMono : MonotoneFamily P) (hB : Bounds P C)
    (hs : 0 ≤ s) (hs1 : s ≤ (1 / 2 : ℝ)) (hw : 0 ≤ w) (hR : Restricted P s w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ ρ : ℝ, 0 < δ → δ ≤ ρ → ρ ≤ (1 / 100 : ℝ) →
      ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (U : ENNReal),
      P (δ ^ η) ρ m (δ ^ (-η)) n U →
      ENNReal.ofReal (coefficient s w 0 (a * δ ^ ε) ρ m 1 n) ≤ U := by
  obtain ⟨a, ha, η₀, hη₀, hR⟩ := hR ε hε
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  let θ : ℝ := ε / 12
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let η : ℝ := min (θ * η₀) (ε / 2)
  have hη : 0 < η := lt_min (mul_pos hθ hη₀) (by positivity)
  let a' : ℝ := min a C⁻¹
  have ha' : 0 < a' := lt_min ha (by positivity)
  refine ⟨a', ha', η, hη, ?_⟩
  intro δ ρ hδ hδρ hρ100 m hm n U hP
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hρ1 : ρ ≤ 1 := by linarith
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  obtain ⟨hn0, hpack, hcount, hU⟩ := hB _ _ _ _ hρ hρ100 hm n U hP
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  by_cases hscale : ρ ≤ δ ^ θ
  · have hden : ρ ^ η₀ ≤ δ ^ η := by
      calc
        _ ≤ (δ ^ θ) ^ η₀ := Real.rpow_le_rpow hρ.le hscale hη₀.le
        _ = δ ^ (θ * η₀) := (Real.rpow_mul hδ.le _ _).symm
        _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
    have hf : δ ^ (-η) ≤ ρ ^ (-η₀) := by
      rw [Real.rpow_neg hδ.le, Real.rpow_neg hρ.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hρ _) hden
    have hP' := hMono _ _ _ _ _ _ hden hf n U hP
    have hr : ENNReal.ofReal (coefficient s w ε a ρ m 1 n) ≤ U := by
      simpa only [coefficient, mul_one] using hR ρ hρ hρ100 m hm n U hP'
    apply le_trans (ENNReal.ofReal_le_ofReal _) hr
    unfold coefficient
    rw [add_zero, Real.rpow_add hρ]
    have he : δ ^ ε ≤ ρ ^ ε := Real.rpow_le_rpow hδ.le hδρ hε.le
    have hm0 : 0 < m := zero_lt_one.trans_le hm
    calc
      _ = a' * δ ^ ε * ρ ^ w * m⁻¹ * ((n : ℝ) * ρ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * 1 * ((n : ℝ) * ρ)) ^ (-s) := rfl
      _ ≤ a * ρ ^ ε * ρ ^ w * m⁻¹ * ((n : ℝ) * ρ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * 1 * ((n : ℝ) * ρ)) ^ (-s) := by
        gcongr
        exact min_le_left _ _
      _ = _ := by ring
  · have hsc : δ ^ θ ≤ ρ := (lt_of_not_ge hscale).le
    have h6 : δ ^ ε ≤ δ ^ η * ρ ^ 6 := by
      calc
        _ ≤ δ ^ (η + θ * 6) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
          have hηε := min_le_right (θ * η₀) (ε / 2)
          dsimp [η, θ] at *
          linarith)
        _ = δ ^ η * (δ ^ θ) ^ 6 := by
          rw [Real.rpow_add hδ]
          congr 1
          exact Real.rpow_mul_natCast hδ.le θ 6
        _ ≤ δ ^ η * ρ ^ 6 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hsc 6) (Real.rpow_nonneg hδ.le _)
    have haC : a' * C ≤ 1 := by
      calc
        _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC0.le
        _ = 1 := inv_mul_cancel₀ hC0.ne'
    have hcard : a' * (n : ℝ) * ρ ^ 4 ≤ 1 := by
      calc
        _ = a' * ((n : ℝ) * ρ ^ 4) := by ring
        _ ≤ a' * C := mul_le_mul_of_nonneg_left hpack ha'.le
        _ ≤ 1 := haC
    have htarget : a' * δ ^ ε * (n : ℝ) ≤ δ ^ η * ρ ^ 2 := by
      calc
        _ ≤ a' * (δ ^ η * ρ ^ 6) * (n : ℝ) := by gcongr
        _ = (δ ^ η * ρ ^ 2) * (a' * (n : ℝ) * ρ ^ 4) := by ring
        _ ≤ (δ ^ η * ρ ^ 2) * 1 := mul_le_mul_of_nonneg_left hcard (by positivity)
        _ = _ := mul_one _
    have hc := coefficient_le_card (s := s) (w := w) (ε := 0) (a := a' * δ ^ ε)
      hs (by linarith) (by linarith) (by simpa) (by positivity) hρ hρ1 hm le_rfl
      (by exact_mod_cast hn0 : (1 : ℝ) ≤ n)
    exact (ENNReal.ofReal_le_ofReal (hc.trans htarget)).trans hU

/-- The abstract transfer used by the two geometric children of slab removal. -/
theorem transfer {P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop}
    {C s w : ℝ} (hC : 1 ≤ C) (hMono : MonotoneFamily P) (hB : Bounds P C)
    (hRed : Reduction P) (hs : 0 < s) (hs1 : s ≤ (1 / 2 : ℝ)) (hw : 0 < w)
    (hR : Restricted P s w) : General P s w := by
  intro ε hε
  obtain ⟨a, ha, η₀, hη₀, hRel⟩ :=
    restricted_relative hC hMono hB hs.le hs1 hw.le hR (show 0 < ε / 4 by positivity)
  let ζ : ℝ := min η₀ (min 1 (ε / (4 * (w + 3))))
  have hζ : 0 < ζ := lt_min hη₀ (lt_min zero_lt_one (by positivity))
  have hζη : ζ ≤ η₀ := min_le_left _ _
  have hζ1 : ζ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hζε : ζ * (w + 3) ≤ ε / 2 := by
    have hh : ζ ≤ ε / (4 * (w + 3)) := (min_le_right _ _).trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (w + 3))).mp hh
    nlinarith
  obtain ⟨η, hη, δ₀, hδ₀, hδ₀100, hRed⟩ := hRed ζ hζ
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  let b : ℝ := (δ₀ ^ η * δ₀ ^ 2) * δ₀ ^ 4 / C
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨min a b, lt_min ha hb, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n U hP
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨hn0, hpack, hcount, hU⟩ := hB _ _ _ _ hδ hδ100 hm n U hP
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  change ENNReal.ofReal (coefficient s w ε (min a b) δ m l n) ≤ U
  by_cases hsmall : δ ≤ δ₀
  · obtain ⟨k, N, hk, hN, ρ, t, M, hscale, hρ100, ht, hM, V, hV, htrans, hconv, hslab, hpacking⟩ :=
      hRed δ hδ hsmall m l hm hl n U hP
    have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ (1 + ζ)).trans_le hscale
    have hM0 : 0 < M := zero_lt_one.trans_le hM
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hδ₂ρ : δ ^ 2 ≤ ρ := by
      calc
        _ = δ ^ (2 : ℝ) := (Real.rpow_two _).symm
        _ ≤ δ ^ (1 + ζ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ ≤ _ := hscale
    have hden : (δ ^ 2) ^ η₀ ≤ δ ^ ζ := by
      rw [← Real.rpow_two, ← Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hf : δ ^ (-ζ) ≤ (δ ^ 2) ^ (-η₀) := by
      rw [Real.rpow_neg hδ.le, Real.rpow_neg (sq_nonneg δ)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (sq_pos_of_pos hδ) _) hden
    have hpowers : (δ ^ 2) ^ (ε / 4) = δ ^ (ε / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hδ.le]
      congr 1
      ring
    have hlocal : ∀ j, ENNReal.ofReal (coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N) ≤ V j := by
      intro j
      have hP' := hMono _ _ _ _ _ _ hden hf N (V j) (hV j)
      simpa only [hpowers] using hRel (δ ^ 2) ρ (sq_pos_of_pos hδ) hδ₂ρ hρ100 M hM N (V j) hP'
    have hsum : ENNReal.ofReal ((k : ℝ) * coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N) ≤
        ∑ j, V j := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlocal j)
    have hcoef := coefficient_geometric_transfer hs.le hs1 hw.le ha hδ hδ1
      hm0 hl0 hn hk' hN' hρ ht hM0 hζ.le hζε hscale hconv hslab hpacking
    have hfull : ENNReal.ofReal (coefficient s w ε a δ m l n) ≤ U := by
      apply le_trans (ENNReal.ofReal_le_ofReal hcoef)
      calc
        ENNReal.ofReal (δ ^ ζ * t * (k : ℝ) * coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N) =
            ENNReal.ofReal (δ ^ ζ * t) *
              ENNReal.ofReal ((k : ℝ) * coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        _ ≤ ENNReal.ofReal (δ ^ ζ * t) * ∑ j, V j := by gcongr
        _ ≤ U := htrans
    apply le_trans (ENNReal.ofReal_le_ofReal _) hfull
    unfold coefficient
    gcongr
    exact min_le_left _ _
  · have hδ₀δ : δ₀ ≤ δ := (lt_of_not_ge hsmall).le
    have hnp : (n : ℝ) * δ₀ ^ 4 ≤ C :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ₀.le hδ₀δ 4) hn.le).trans hpack
    have hbn : b * (n : ℝ) ≤ δ₀ ^ η * δ₀ ^ 2 := by
      calc
        _ = (δ₀ ^ η * δ₀ ^ 2) * (((n : ℝ) * δ₀ ^ 4) / C) := by dsimp [b]; ring
        _ ≤ (δ₀ ^ η * δ₀ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hC0).mpr hnp) (by positivity)
        _ = _ := mul_one _
    have hc := coefficient_le_card (s := s) (w := w) (ε := ε) (a := min a b)
      hs.le (by linarith) (by linarith) (by positivity) (lt_min ha hb).le hδ hδ1 hm hl
      (by exact_mod_cast hn0 : (1 : ℝ) ≤ n)
    apply le_trans (ENNReal.ofReal_le_ofReal _) hU
    exact hc.trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le).trans
      (hbn.trans (mul_le_mul (Real.rpow_le_rpow hδ₀.le hδ₀δ hη.le)
        (pow_le_pow_left₀ hδ₀.le hδ₀δ 2) (sq_nonneg δ₀) (Real.rpow_nonneg hδ.le _))))

end WangZahlLot.Obl.wz_small_slab_error_removal.Model
