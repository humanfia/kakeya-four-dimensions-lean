-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.DenseRestriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedInitialization
import Submission.WZ.Obl.wz_multiscale_finite_tower.PowerErrors

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma AlignedFamily.mass_lower {d lam K L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (H : AlignedFamily d lam K L u h n x v Y) :
    ENNReal.ofReal (lam * n * d ^ 2) ≤ ∑ i, volume (Y i) := by
  calc
    _ = ∑ _i : Fin n, ENNReal.ofReal (lam * d ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => H.density i

lemma AlignedFamily.card_bound {d lam K L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (H : AlignedFamily d lam K L u h n x v Y) (hK : 0 ≤ K) :
    (n : ℝ) * d ^ 2 ≤ 56 * K := by
  let W := Tube 1 (- (1 / 2 : ℝ) • u) u
  have hW : ∀ i, Tube d (x i) (v i) ⊆ W :=
    fun i => (H.ball i).trans (centered_root_contains_ball u)
  have hh := H.count W ((convex_segment _ _).thickening 1)
  have he : {i | Tube d (x i) (v i) ⊆ W} = Set.univ := Set.eq_univ_iff_forall.mpr hW
  rw [he, Set.ncard_univ, Nat.card_fin] at hh
  have hv : volume W ≤ ENNReal.ofReal 56 := by
    simpa [W] using WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl (- (1 / 2 : ℝ) • u) u H.root_unit
  have hb := hh.trans (mul_le_mul' le_rfl hv)
  rw [← ENNReal.ofReal_mul hK] at hb
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (by norm_num : (0 : ℝ) ≤ 56))).mp hb
  linarith

lemma AlignedFamily.reindex {d lam lam' K L L' h : ℝ} {u : Space} {n m : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (H : AlignedFamily d lam K L u h n x v Y)
    (e : Fin m → Fin n) (he : Function.Injective e) (hm : 0 < m)
    (Z : Fin m → Set Space) (hZm : ∀ i, MeasurableSet (Z i))
    (hZY : ∀ i, Z i ⊆ Y (e i))
    (hden : ∀ i, ENNReal.ofReal (lam' * d ^ 2) ≤ volume (Z i))
    (hL : L * n ≤ L' * m) :
    AlignedFamily d lam' K L' u h m (x ∘ e) (v ∘ e) Z := by
  refine ⟨hm, fun i => H.unit (e i), fun i => H.ball (e i), hZm,
    fun i => (hZY i).trans (H.shading (e i)), hden, H.count.comp e he, ?_,
    H.root_unit, fun i => H.direction_cap (e i), fun i => H.aligned (e i), fun i => H.midpoint (e i)⟩
  simpa only [Function.comp_def] using slabBound_comp H.slab e he hL

/-- Pointwise density can be restored after a measurable mass restriction. -/
theorem heavy_shadings {d lam : ℝ} (hd : 0 < d) (hlam : 0 < lam) {n : ℕ} (hn : 0 < n)
    (Y : Fin n → Set Space) (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (hmass : ENNReal.ofReal (lam * n * d ^ 2) ≤ ∑ i, volume (Y i)) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i) ∧
      ∀ i ∈ S, ENNReal.ofReal (lam / 2 * d ^ 2) ≤ volume (Y i) := by
  classical
  have hsumfin : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
  have hsum : (∑ i, volume (Y i)).toReal = ∑ i, (volume (Y i)).toReal :=
    ENNReal.toReal_sum (fun i _ => hfin i)
  have hlow : lam * n * d ^ 2 ≤ ∑ i, (volume (Y i)).toReal := by
    simpa only [hsum] using (ENNReal.ofReal_le_iff_le_toReal hsumfin).mp hmass
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < ∑ i, (volume (Y i)).toReal :=
    (by positivity : 0 < lam * n * d ^ 2).trans_le hlow
  obtain ⟨S, hS, hret, hpoint⟩ := heavy_weights hn (fun i => (volume (Y i)).toReal) hpos
  refine ⟨S, hS, ?_, ?_⟩
  · apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) hsumfin)
      (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))).mp
    rw [ENNReal.toReal_mul, hsum, ENNReal.toReal_sum (fun i _ => hfin i)]
    norm_num
    linarith
  · intro i hi
    apply (ENNReal.ofReal_le_iff_le_toReal (hfin i)).mpr
    apply le_trans _ (hpoint i hi)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith

lemma retained_subset_cardinality {d lam τ : ℝ} (hd : 0 < d) (hτ : 0 ≤ τ)
    {n : ℕ} {Y Z : Fin n → Set Space} (S : Finset (Fin n))
    (hlower : ENNReal.ofReal (lam * n * d ^ 2) ≤ ∑ i, volume (Y i))
    (hupper : ∀ i ∈ S, volume (Z i) ≤ ENNReal.ofReal (56 * d ^ 2))
    (hret : ENNReal.ofReal τ * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i)) :
    (τ * lam / 56) * n ≤ S.card := by
  have hu : (∑ i ∈ S, volume (Z i)) ≤ ENNReal.ofReal (56 * S.card * d ^ 2) := by
    calc
      _ ≤ ∑ _i ∈ S, ENNReal.ofReal (56 * d ^ 2) := Finset.sum_le_sum hupper
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
        congr 1
        ring
  have hh := ((mul_le_mul' le_rfl hlower).trans hret).trans hu
  rw [← ENNReal.ofReal_mul hτ] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56 * (S.card : ℝ) * d ^ 2)).mp hh
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp
  nlinarith only [hr]

end WangZahlLot.Obl.wz_multiscale_finite_tower
