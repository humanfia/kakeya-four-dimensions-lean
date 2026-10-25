-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.CellRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Cells
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.IncidenceEnumeration
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.ShadingRefinement
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file CellRefinement.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridUnion)

/-- The incidence-weighted cell selection and the literal Frostman refinement,
with all quantitative losses displayed. -/
theorem Factored.cell_refinement {D b s L Q : ℝ} {n p : ℕ}
    {T : Fin n → Set Space} {P : Fin p → Set Space}
    (hf : Factored D b T P) (hn : 0 < n) (hs : 0 < s) (hs1 : s ≤ 1)
    (hL : 0 < L) (hLQ : L ≤ Q) (Y : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYB : ∀ i, Y i ⊆ Metric.ball 0 1)
    (hupper : ∀ i, volume (Y i) ≤ ENNReal.ofReal Q)
    (hden : ∀ i, ENNReal.ofReal L ≤ volume (Y i))
    {K : ℕ} (hK : 0 < K) (hKlarge : 18522 * (1 / 2 : ℝ) ^ K ≤ L) :
    ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ) (k q : ℕ)
      (g : Fin k → Fin n) (h : Fin q → Fin p),
      (1 / 2 : ℝ) ^ (K + 1) ≤ t ∧
      (∀ z ∈ S, ENNReal.ofReal (t * (27 * s ^ 3)) ≤ volume ((⋃ i, Y i) ∩ block s z) ∧
        volume ((⋃ i, Y i) ∩ block s z) ≤ ENNReal.ofReal (2 * t * (27 * s ^ 3))) ∧
      0 < k ∧ 0 < q ∧ Function.Injective g ∧ Function.Injective h ∧
      (∀ i, ENNReal.ofReal (L / (8 * K)) ≤ volume (Y (g i) ∩ gridUnion s S)) ∧
      Factored (16 * K * Q * D ^ 2 / L) b (T ∘ g) (P ∘ h) ∧
      ∀ j, L ^ 2 / (256 * (K : ℝ) ^ 2 * Q ^ 2 * D) * n ≤
        (q : ℝ) * Set.ncard {i | T (g i) ⊆ P (h j)} := by
  classical
  have hQ : 0 < Q := hL.trans_le hLQ
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (Nat.succ_le_iff.mpr hK)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (hf.one_le_error hn)
  let F : Fin p → Finset (Fin n) := fun j => {i | T i ⊆ P j}.toFinset
  have hFcard (j : Fin p) : (F j).card = Set.ncard {i | T i ⊆ P j} := by
    simp only [F, Set.ncard_eq_toFinset_card']
  obtain ⟨N, hN, r, hr, hNcard, hsum, hunion⟩ := incidence_enumeration hn F (by
    intro i
    obtain ⟨j, hj⟩ := hf.1 i
    exact ⟨j, by simpa only [F, Set.mem_toFinset, Set.mem_ofPred_eq] using hj⟩)
  have hNreal : (N : ℝ) = ∑ j, ((F j).card : ℝ) := by exact_mod_cast hNcard
  have hmass : ENNReal.ofReal (L * N) ≤ ∑ a, volume (Y (r a)) := by
    rw [hsum (fun i => volume (Y i)), hNreal]
    exact uniform_incidence_mass F Y hL.le hden
  obtain ⟨S, t, ht, hdense, hret⟩ := cell_density_pigeonhole hs hs1 (by positivity : 0 < L * N)
    (fun a => Y (r a)) (fun a => hYm (r a)) (fun a => hYB (r a)) hmass hK (by
      have h := mul_le_mul_of_nonneg_right hKlarge (Nat.cast_nonneg N)
      nlinarith only [h])
  have hdense' : ∀ z ∈ S,
      ENNReal.ofReal (t * (27 * s ^ 3)) ≤ volume ((⋃ i, Y i) ∩ block s z) ∧
      volume ((⋃ i, Y i) ∩ block s z) ≤ ENNReal.ofReal (2 * t * (27 * s ^ 3)) := by
    simpa only [hunion Y] using hdense
  let d := L / (4 * K * Q)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    rw [div_le_iff₀ (by positivity : 0 < 4 * K * Q)]
    nlinarith [mul_le_mul_of_nonneg_right hK1 hQ.le]
  have hret' : ENNReal.ofReal (d * Q * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ))) ≤
      ∑ j, ∑ i ∈ {i | T i ⊆ P j}.toFinset, volume (Y i ∩ gridUnion s S) := by
    rw [hsum (fun i => volume (Y i ∩ gridUnion s S))] at hret
    have he : d * Q * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ)) = L * N / (4 * K) := by
      rw [hNreal]
      simp only [hFcard]
      dsimp [d]
      field_simp <;> ring
    rw [he]
    exact hret
  obtain ⟨k, q, g, h, hk, hq, hg, hh, hpoint, hfact, hprod⟩ :=
    hf.dense_shading_refinement hn hd hd1 hQ (fun i => Y i ∩ gridUnion s S)
      (fun i => (measure_mono inter_subset_left).trans (hupper i)) hret'
  have hpointcoeff : d / 2 * Q = L / (8 * K) := by dsimp [d]; field_simp <;> ring
  have herror : 4 * D ^ 2 / d = 16 * K * Q * D ^ 2 / L := by
    dsimp [d]
    field_simp <;> ring
  have hprodcoeff : d ^ 2 / (16 * D) = L ^ 2 / (256 * (K : ℝ) ^ 2 * Q ^ 2 * D) := by
    dsimp [d]
    field_simp <;> ring
  refine ⟨S, t, k, q, g, h, ht, hdense', hk, hq, hg, hh, ?_, ?_, ?_⟩
  · simpa only [hpointcoeff] using hpoint
  · simpa only [herror] using hfact
  · simpa only [hprodcoeff] using hprod

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
