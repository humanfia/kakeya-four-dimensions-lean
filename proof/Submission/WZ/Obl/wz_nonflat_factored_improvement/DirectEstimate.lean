-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.DirectEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.RealWeight
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Counts

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set

/-- Direct use of `D` on the retained factorization when its convex count is small. -/
theorem direct_retained_estimate {σ ω : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 2 / 3)
    (hD : EstimateD σ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ ν δ m c : ℝ, 0 < ν → 2 * ν ≤ η → 0 < δ → δ ≤ 1 / 100 →
      1 ≤ m → c ≤ δ ^ (-η) →
      ∀ (n k : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (g : Fin k → Fin n),
      0 < n → Function.Injective g → δ ^ ν * n ≤ k →
      (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i)) →
      ConvexCount δ c (fun i => x (g i)) (fun i => v (g i)) →
      SlabCount δ (δ ^ (-2 * ν)) (fun i => x (g i)) (fun i => v (g i)) →
      ENNReal.ofReal (A * δ ^ (ω + ε + ν) * weight σ δ m n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨A, hA, η, hη, H⟩ := hD ε hε
  refine ⟨A, η, hA, hη, ?_⟩
  intro ν δ m c hν hνη hδ hδ100 hm hc n k x v Y g hn hg hsize hv hball hover hYm hYT hind hconv hslab
  have hδ1 : δ ≤ 1 := by linarith
  have hf : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ ν
  have hf1 : δ ^ ν ≤ 1 := Real.rpow_le_one hδ.le hδ1 hν.le
  have hk0 : 0 < (k : ℝ) := (mul_pos hf (Nat.cast_pos.mpr hn)).trans_le hsize
  have hk : 0 < k := Nat.cast_pos.mp hk0
  have hden : ∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i) := by
    intro i
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (sq_nonneg δ))).trans (hind i)
  have hs : δ ^ (-2 * ν) ≤ δ ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hd := H δ hδ hδ100 k (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i))
    hk (fun i => hv (g i)) (fun i => hball (g i)) (fun i j hij => hover (g i) (g j) (hg.ne hij))
    (fun i => hYm (g i)) (fun i => hYT (g i)) (subfamily_density hδ.le g hden)
    (convexCount_mono hc hconv) (slabCount_mono hs hslab)
  have hw := realWeight_fraction hδ zero_lt_one (Nat.cast_pos.mpr hn) hf hf1 hsize hσ0 (by linarith : σ ≤ 1)
  change δ ^ ν * weight σ δ 1 n ≤ weight σ δ 1 k at hw
  have hwm := weight_mono_coefficient hδ zero_lt_one hm hσ1 n
  have hwm' : δ ^ ν * weight σ δ m n ≤ weight σ δ 1 k :=
    (mul_le_mul_of_nonneg_left hwm hf.le).trans hw
  have he : weight σ δ 1 k = (k : ℝ) * δ ^ 2 * ((k : ℝ) * δ) ^ (-σ) := by simp [weight]
  rw [he] at hwm'
  apply le_trans (b := volume (⋃ i, Y (g i))) _ (subfamily_union_volume Y g)
  apply le_trans (ENNReal.ofReal_le_ofReal _) hd
  rw [Real.rpow_add hδ]
  convert mul_le_mul_of_nonneg_left hwm' (by positivity : 0 ≤ A * δ ^ (ω + ε)) using 1 <;> ring

/-- The product target is no larger than the direct fine-scale target. -/
theorem product_scalar_le_direct {δ b ω u e s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδb : δ ≤ b) (hb1 : b ≤ 1) (hgap : ω ≤ u) (he : 0 ≤ e) (hse : s ≤ e) :
    δ ^ (u + e) * b ^ (ω - u + e) ≤ δ ^ (ω + s) := by
  have hb : 0 < b := hδ.trans_le hδb
  have hbp : b ^ (ω - u) ≤ δ ^ (ω - u) :=
    Real.rpow_le_rpow_of_nonpos hδ hδb (by linarith)
  have hbe : b ^ e ≤ 1 := Real.rpow_le_one hb.le hb1 he
  rw [Real.rpow_add hb]
  calc
    _ ≤ δ ^ (u + e) * (δ ^ (ω - u) * 1) := by gcongr
    _ = δ ^ (ω + e) := by rw [mul_one, ← Real.rpow_add hδ]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
