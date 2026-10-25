-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoverWeights.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseStability
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverSize

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open Finset MeasureTheory

/-- The shading mass carried by a complete coarse fiber, in real coordinates. -/
def coarseWeight {n N : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (k : Fin N) : ℝ :=
  ∑ i ∈ S with f i = k, (μ (Z i)).toReal

theorem coarseWeight_nonneg {n N : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (k : Fin N) : 0 ≤ coarseWeight S Z f k := by
  exact sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- Summing complete fiber weights is exactly restriction to the selected coarse set. -/
theorem sum_coarseWeight {n N : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (Q : Finset (Fin N)) :
    ∑ k ∈ Q, coarseWeight S Z f k = ∑ i ∈ S with f i ∈ Q, (μ (Z i)).toReal := by
  classical
  exact sum_fiberwise_eq_sum_filter S Q f (fun i => (μ (Z i)).toReal)

theorem sum_coarseWeight_univ {n N : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) :
    ∑ k, coarseWeight S Z f k = ∑ i ∈ S, (μ (Z i)).toReal := by
  simpa using sum_coarseWeight S Z f univ

theorem a_shading_ne_top {δ η m l : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} (hA : A δ η m l n x v Y) (i : Fin n) :
    μ (Y i) ≠ ⊤ := by
  exact (lt_of_le_of_lt
    (measure_mono ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1))
    (measure_ball_lt_top : volume (Metric.ball (0 : V) 1) < ⊤)).ne

theorem c_subshading_ne_top {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) (i : Fin n) :
    μ (Z i) ≠ ⊤ :=
  ne_top_of_le_ne_top (a_shading_ne_top hA i) (measure_mono (hC.1 i).2.1)

/-- `A` gives a finite, positive reference mass and its real density inequality. -/
theorem a_real_density {δ η m l : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} (hδ : 0 < δ)
    (hA : A δ η m l n x v Y) :
    δ ^ η * n * δ ^ 2 ≤ ∑ i, (μ (Y i)).toReal := by
  have hh := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i _ => a_shading_ne_top hA i)) hA.2.2.2.1
  simpa only [o, ENNReal.toReal_ofReal (by positivity : 0 ≤ δ ^ η * n * δ ^ 2),
    ENNReal.toReal_sum (fun i _ => a_shading_ne_top hA i)] using hh

theorem c_coarse_pos {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    0 < N := by
  obtain ⟨i, _⟩ := c_fine_nonempty hδ hA hC
  exact Nat.zero_lt_of_lt (f i).isLt

/-- The original retained shading mass is the lower bound for the coarse weights. -/
theorem c_coarseWeight_retention {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    δ ^ h * (∑ i, (μ (Y i)).toReal) ≤ ∑ k, coarseWeight S Z f k := by
  rw [sum_coarseWeight_univ]
  have hh := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i _ => c_subshading_ne_top hA hC i)) hC.2.1
  simpa only [o, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
    ENNReal.toReal_sum (fun i _ => a_shading_ne_top hA i),
    ENNReal.toReal_sum (fun i _ => c_subshading_ne_top hA hC i)] using hh

theorem c_coarseWeight_density {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    δ ^ (h + η) * n * δ ^ 2 ≤ ∑ k, coarseWeight S Z f k := by
  calc
    _ = δ ^ h * (δ ^ η * n * δ ^ 2) := by rw [Real.rpow_add hδ]; ring
    _ ≤ δ ^ h * (∑ i, (μ (Y i)).toReal) :=
      mul_le_mul_of_nonneg_left (a_real_density hδ hA) (Real.rpow_nonneg hδ.le _)
    _ ≤ _ := c_coarseWeight_retention hδ hA hC

/-- Balance of fine cardinalities and the tube-volume bound control each coarse weight. -/
theorem c_coarseWeight_upper {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : A δ η m l n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f) (k : Fin N) :
    coarseWeight S Z f k ≤ 384 * δ ^ (-h) * n * δ ^ 2 / N := by
  classical
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (c_coarse_pos hδ hA hC)
  have hweights (i) (_hi : i ∈ S) : (μ (Z i)).toReal ≤ 384 * δ ^ 2 := by
    have hbound : μ (Z i) ≤ o (384 * δ ^ 2) :=
      (measure_mono ((hC.1 i).2.1.trans (hA.2.1 i).2.2.2)).trans
        (tube_volume_upper hδ hδ1 (x i) (v i) (hA.2.1 i).1)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [o, ENNReal.toReal_ofReal (by positivity : 0 ≤ 384 * δ ^ 2)] using hh
  have hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      δ ^ (-h) * (S.filter (fun i => f i = k')).card := by
    intro k k'
    have hh := hC.2.2.2.2.2.2.1 k k'
    simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hh
  have hh := selected_fiber_mass_le S {k} f (fun i => (μ (Z i)).toReal)
    (by positivity : 0 ≤ 384 * δ ^ 2) hweights hbal
  simp only [mem_singleton, card_singleton, Nat.cast_one, mul_one, Fintype.card_fin] at hh
  apply (le_div_iff₀ hN).mpr
  calc
    coarseWeight S Z f k * N ≤ 384 * δ ^ 2 * δ ^ (-h) * S.card := hh
    _ ≤ 384 * δ ^ 2 * δ ^ (-h) * n := by
      gcongr
      exact_mod_cast (show S.card ≤ n by simpa using S.card_le_univ)
    _ = _ := by ring

/-- Real coarse mass equals the finite ENNReal mass of the retained fine family. -/
theorem ofReal_sum_coarseWeight {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (Q : Finset (Fin N)) :
    o (∑ k ∈ Q, coarseWeight S Z f k) = ∑ i ∈ S with f i ∈ Q, μ (Z i) := by
  classical
  rw [sum_coarseWeight, ← ENNReal.toReal_sum (fun i _ => c_subshading_ne_top hA hC i)]
  exact ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr (fun i _ => c_subshading_ne_top hA hC i))

/-- A weighted selection relative to the coarse mass retains the corresponding product
of powers of the original shading mass. Complete fibers are retained. -/
theorem c_retention_of_weight_retention {δ η m l h ρ τ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (Q : Finset (Fin N))
    (hkeep : δ ^ τ * (∑ k, coarseWeight S Z f k) ≤ ∑ k ∈ Q, coarseWeight S Z f k) :
    o (δ ^ (τ + h)) * ∑ i, μ (Y i) ≤ ∑ i ∈ S with f i ∈ Q, μ (Z i) := by
  have hh : δ ^ (τ + h) * (∑ i, (μ (Y i)).toReal) ≤
      ∑ k ∈ Q, coarseWeight S Z f k := by
    calc
      _ = δ ^ τ * (δ ^ h * (∑ i, (μ (Y i)).toReal)) := by
        rw [Real.rpow_add hδ, mul_assoc]
      _ ≤ δ ^ τ * (∑ k, coarseWeight S Z f k) :=
        mul_le_mul_of_nonneg_left (c_coarseWeight_retention hδ hA hC)
          (Real.rpow_nonneg hδ.le _)
      _ ≤ _ := hkeep
  have he : o (∑ i, (μ (Y i)).toReal) = ∑ i, μ (Y i) := by
    rw [← ENNReal.toReal_sum (fun i _ => a_shading_ne_top hA i)]
    exact ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr (fun i _ => a_shading_ne_top hA i))
  have hh' := ENNReal.ofReal_le_ofReal hh
  rwa [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← o, he,
    ofReal_sum_coarseWeight hA hC Q] at hh'

/-- The threshold `δ²` discards at most half of the coarse mass once the density and
balance errors fit in one power of `δ`. -/
theorem c_coarseWeight_tail {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (herr : η + 2 * h ≤ 1) (hsmall : 768 * δ ≤ 1)
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    δ ^ 2 * (384 * δ ^ (-h) * n * δ ^ 2 / N) * N ≤
      (∑ k, coarseWeight S Z f k) / 2 := by
  have hN : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr (c_coarse_pos hδ hA hC)).ne'
  have hexp : δ ^ (2 - h) ≤ δ ^ (h + η + 1) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have he : δ ^ (2 : ℕ) * δ ^ (-h) = δ ^ (2 - h) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ]
    congr 1
  calc
    _ = 384 * (δ ^ (2 : ℕ) * δ ^ (-h)) * n * δ ^ 2 := by field_simp
    _ = 384 * δ ^ (2 - h) * n * δ ^ 2 := by rw [he]
    _ ≤ 384 * δ ^ (h + η + 1) * n * δ ^ 2 := by gcongr
    _ = (384 * δ) * (δ ^ (h + η) * n * δ ^ 2) := by
      rw [Real.rpow_add hδ, Real.rpow_one]
      ring
    _ ≤ (1 / 2) * (δ ^ (h + η) * n * δ ^ 2) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ (1 / 2) * ∑ k, coarseWeight S Z f k :=
      mul_le_mul_of_nonneg_left (c_coarseWeight_density hδ hA hC) (by norm_num)
    _ = _ := by ring

/-- The actual coarse count has the fixed polynomial bound used in stable selection. -/
theorem c_coarse_size_le_sixth_power {δ η h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ ≤ ρ) (hη : η ≤ 2)
    (hsmall : wz_endpoint_bootstrap.ballConstant * δ ≤ 1)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f) :
    (N : ℝ) / ρ ≤ δ ^ (-(6 : ℝ)) := by
  calc
    _ ≤ wz_endpoint_bootstrap.ballConstant * δ ^ (-(η + 3)) :=
      coarse_size_power_bound hδ hδρ hA hC
    _ = (wz_endpoint_bootstrap.ballConstant * δ) * δ ^ (-(η + 4)) := by
      have he : δ * δ ^ (-(η + 4)) = δ ^ (-(η + 3)) := by
        calc
          _ = δ ^ (1 : ℝ) * δ ^ (-(η + 4)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
      rw [mul_assoc, he]
    _ ≤ 1 * δ ^ (-(η + 4)) :=
      mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hδ.le _)
    _ ≤ δ ^ (-(6 : ℝ)) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

/-- Comparable selected fiber masses give a density bound in every selected fiber.
The exponent records mass retention, the original density, mass comparability, and
the balance of the original fiber cardinalities. -/
theorem c_selected_fiber_density {δ η m l h ρ τ ε : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (Q : Finset (Fin N))
    (hkeep : δ ^ τ * (∑ i, (μ (Y i)).toReal) ≤ ∑ j ∈ Q, coarseWeight S Z f j)
    (hcmp : ∀ j ∈ Q, ∀ k ∈ Q, coarseWeight S Z f j ≤ δ ^ (-ε) * coarseWeight S Z f k)
    (k : Fin N) (hk : k ∈ Q) :
    o (δ ^ (τ + η + ε + h) * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
      ∑ i ∈ S with f i = k, μ (Z i) := by
  classical
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (c_coarse_pos hδ hA hC)
  have hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      δ ^ (-h) * (S.filter (fun i => f i = k')).card := by
    intro k k'
    have hh := hC.2.2.2.2.2.2.1 k k'
    simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hh
  have hcount : ((S.filter (fun i => f i = k)).card : ℝ) * N ≤ δ ^ (-h) * n := by
    have hh := balanced_fiber_card_le S f hbal k
    simp only [Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (show S.card ≤ n by simpa using S.card_le_univ))
      (Real.rpow_nonneg hδ.le _))
  have htotal : δ ^ (τ + η) * n * δ ^ 2 ≤ ∑ j ∈ Q, coarseWeight S Z f j := by
    calc
      _ = δ ^ τ * (δ ^ η * n * δ ^ 2) := by rw [Real.rpow_add hδ]; ring
      _ ≤ δ ^ τ * ∑ i, (μ (Y i)).toReal :=
        mul_le_mul_of_nonneg_left (a_real_density hδ hA) (Real.rpow_nonneg hδ.le _)
      _ ≤ _ := hkeep
  have hsum : (∑ j ∈ Q, coarseWeight S Z f j) ≤
      δ ^ (-ε) * coarseWeight S Z f k * N := by
    calc
      _ ≤ ∑ _j ∈ Q, δ ^ (-ε) * coarseWeight S Z f k :=
        sum_le_sum fun j hj => hcmp j hj k hk
      _ = δ ^ (-ε) * coarseWeight S Z f k * Q.card := by simp [mul_comm]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (show Q.card ≤ N by simpa using Q.card_le_univ))
        exact mul_nonneg (Real.rpow_nonneg hδ.le _) (coarseWeight_nonneg S Z f k)
  have heh : δ ^ (τ + η + ε + h) * δ ^ (-h) = δ ^ (τ + η + ε) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have heε : δ ^ ε * δ ^ (-ε) = 1 := by rw [← Real.rpow_add hδ]; simp
  have hreal : δ ^ (τ + η + ε + h) * (S.filter (fun i => f i = k)).card * δ ^ 2 ≤
      coarseWeight S Z f k := by
    apply (mul_le_mul_iff_left₀ hN).mp
    calc
      _ = (δ ^ (τ + η + ε + h) * δ ^ 2) *
          ((S.filter (fun i => f i = k)).card * (N : ℝ)) := by ring
      _ ≤ (δ ^ (τ + η + ε + h) * δ ^ 2) * (δ ^ (-h) * n) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = δ ^ (τ + η + ε) * n * δ ^ 2 := by
        calc
          _ = (δ ^ (τ + η + ε + h) * δ ^ (-h)) * n * δ ^ 2 := by ring
          _ = _ := by rw [heh]
      _ = δ ^ ε * (δ ^ (τ + η) * n * δ ^ 2) := by
        rw [Real.rpow_add hδ]
        ring
      _ ≤ δ ^ ε * (∑ j ∈ Q, coarseWeight S Z f j) :=
        mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg hδ.le _)
      _ ≤ δ ^ ε * (δ ^ (-ε) * coarseWeight S Z f k * N) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hδ.le _)
      _ = coarseWeight S Z f k * N := by rw [← mul_assoc, ← mul_assoc, heε, one_mul]
  have ho := ENNReal.ofReal_le_ofReal hreal
  have hmass : o (coarseWeight S Z f k) = ∑ i ∈ S with f i = k, μ (Z i) := by
    simpa using ofReal_sum_coarseWeight hA hC {k}
  simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset, ← hmass, o] using ho

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
