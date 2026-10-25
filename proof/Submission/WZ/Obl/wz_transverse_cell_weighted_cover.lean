-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Assembly
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_transverse_cell_weighted_cover`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_transverse_cell_weighted_cover/`
belong to this obligation.
-/

theorem WangZahlLot.wz_transverse_cell_weighted_cover : (fun (E:Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasureTheory.MeasureSpace E] => (fun (B:Set E) => (fun (T:ℝ → E → E → Set E) => (fun (P:ℝ → ℝ → E → (Fin 3 → E) → Set E) => (fun (C:ℝ → ℝ → (n:ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop) => (fun (W:ℝ → ℝ → (n:ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop) => ∀ s:ℝ,0 < s → ∃ r:ℝ,0 < r ∧ ∃ δ₀:ℝ,0 < δ₀ ∧ δ₀ ≤ (1/100:ℝ) ∧ ∀ δ:ℝ,0 < δ → δ ≤ δ₀ → ∀ (n:ℕ) (x v:Fin n → E) (Y:Fin n → Set E),C δ (δ ^ r) n x v Y → W δ (δ ^ s) n x v Y) (fun δ h n x v Y => 0 < n ∧ (n:ℝ) ≤ δ ^ (-100:ℝ) ∧ ∃ m:ℕ,0 < m ∧ ∃ ρ:ℝ,0 < ρ ∧ δ * h ≤ ρ ∧ ρ ≤ (1/100:ℝ) ∧ ∃ (M:Fin m → ℕ) (f:Fin m → AffineEquiv ℝ E E) (D:Fin m → ℝ) (z w:(j:Fin m) → Fin (M j) → E) (Z:(j:Fin m) → Fin (M j) → Set E) (F:(j:Fin m) → Fin (M j) → Finset (Fin n)),(∀ j,0 < M j) ∧ (∀ j,δ ^ (100:ℕ) ≤ D j ∧ D j ≤ δ ^ (-100:ℝ)) ∧ (∀ j (Q:Set E),MeasureTheory.volume (f j '' Q) = ENNReal.ofReal (D j) * MeasureTheory.volume Q) ∧ (∀ j a,‖w j a‖ = 1) ∧ (∀ j a,T ρ (z j a) (w j a) ⊆ B) ∧ (∀ j a b,a ≠ b → MeasureTheory.volume (T ρ (z j a) (w j a) ∩ T ρ (z j b) (w j b)) ≤ (1/2:ENNReal) * MeasureTheory.volume (T ρ (z j a) (w j a))) ∧ (∀ j a,MeasurableSet (Z j a)) ∧ (∀ j a,Z j a ⊆ T ρ (z j a) (w j a)) ∧ (∀ j a,ENNReal.ofReal (h * ρ ^ 2) ≤ MeasureTheory.volume (Z j a)) ∧ (∀ j a,(F j a).Nonempty) ∧ (∀ j a b,a ≠ b → Disjoint (F j a) (F j b)) ∧ (∀ j a i,i ∈ F j a → T δ (x i) (v i) ⊆ f j '' T ρ (z j a) (w j a)) ∧ h * (n:ℝ) ≤ Finset.sum Finset.univ (fun j => Finset.sum Finset.univ (fun a => ((F j a).card:ℝ))) ∧ (∀ j (ν:E) (s r:ℝ),‖ν‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i:Fin n | ∃ a:Fin (M j),i ∈ F j a ∧ T ρ (z j a) (w j a) ⊆ (B ∩ {p | |inner ℝ ν p - s| ≤ r})}:ℝ) ≤ ENNReal.ofReal (h⁻¹ * Finset.sum Finset.univ (fun a => ((F j a).card:ℝ))) * MeasureTheory.volume (B ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧ Finset.sum Finset.univ (fun j => ENNReal.ofReal (D j) * MeasureTheory.volume (⋃ a,Z j a)) ≤ MeasureTheory.volume (⋃ i,Y i))) (fun δ h n x v Y => 0 < n ∧ (n:ℝ) ≤ δ ^ (-100:ℝ) ∧ ∃ m:ℕ,0 < m ∧ ∃ (I:Fin m → Finset (Fin n)) (f:Fin m → AffineEquiv ℝ E E) (D:Fin m → ℝ) (a b:ℝ) (c:Fin m → Fin n → E) (u:Fin m → Fin n → Fin 3 → E) (H:Fin m → Fin n → Set E),δ ^ (100:ℕ) ≤ a ∧ a ≤ b ∧ b ≤ (1/1000000:ℝ) ∧ δ * h ≤ b ∧ (∀ j,(I j).Nonempty) ∧ h * (n:ℝ) ≤ Finset.sum Finset.univ (fun j => ((I j).card:ℝ)) ∧ (∀ j,δ ^ (100:ℕ) ≤ D j ∧ D j ≤ δ ^ (-100:ℝ)) ∧ (∀ j (Q:Set E),MeasureTheory.volume (f j '' Q) = ENNReal.ofReal (D j) * MeasureTheory.volume Q) ∧ (∀ j i,i ∈ I j → Orthonormal ℝ (u j i)) ∧ (∀ j i,i ∈ I j → P a b (c j i) (u j i) ⊆ Metric.ball (0:E) (1/100)) ∧ (∀ j i,i ∈ I j → T δ (x i) (v i) ⊆ f j '' P a b (c j i) (u j i)) ∧ (∀ j i,i ∈ I j → MeasurableSet (H j i)) ∧ (∀ j i,i ∈ I j → H j i ⊆ P a b (c j i) (u j i) ∩ f j ⁻¹' (Y i)) ∧ (∀ j i,i ∈ I j → ENNReal.ofReal h * MeasureTheory.volume (P a b (c j i) (u j i)) ≤ MeasureTheory.volume (H j i)) ∧ (∀ j i,i ∈ I j → ∀ p:E,p ∈ H j i → ∀ r:ℝ,a ≤ r → r ≤ 1 → ENNReal.ofReal h * MeasureTheory.volume (P a b (c j i) (u j i) ∩ Metric.ball p r) ≤ MeasureTheory.volume (H j i ∩ Metric.ball p r)) ∧ (∀ j (p:E),(∃ i:Fin n,i ∈ I j ∧ p ∈ H j i) → ∃ i i':Fin n,i ∈ I j ∧ i' ∈ I j ∧ p ∈ H j i ∧ p ∈ H j i' ∧ h ≤ a / b + min ‖u j i 0 - u j i' 0‖ ‖u j i 0 + u j i' 0‖) ∧ (∀ j (ν:E) (s r:ℝ),‖ν‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i:Fin n | i ∈ I j ∧ P a b (c j i) (u j i) ⊆ (B ∩ {p | |inner ℝ ν p - s| ≤ r})}:ℝ) ≤ ENNReal.ofReal (h⁻¹ * ((I j).card:ℝ)) * MeasureTheory.volume (B ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧ (∀ j j',j ≠ j' → Disjoint (f j '' (⋃ i ∈ I j,H j i)) (f j' '' (⋃ i ∈ I j',H j' i))))) (fun a b c u => {p | |inner ℝ (u 0) (p - c)| ≤ a ∧ |inner ℝ (u 1) (p - c)| ≤ b ∧ |inner ℝ (u 2) (p - c)| ≤ (1/1000:ℝ)})) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) (Metric.ball (0:E) 1)) LeanEval.Analysis.WangZahlKakeya.Space := by
  open WangZahlLot.Obl.wz_transverse_cell_weighted_cover in
  intro s hs
  -- the constant of `cell_density` and the choice of `δ₀`, for `r = s / 16`
  obtain ⟨Cd, hCd, hcell⟩ := cell_density
  obtain ⟨δ₀, hδ₀, hδ₀1, hA⟩ := asm_exists_delta hs hCd
  refine ⟨s / 16, by positivity, δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδδ₀ n x v Y hC
  obtain ⟨hh0, hh1, hs0, hss, hA1, hA2⟩ := hA δ hδ hδδ₀
  obtain ⟨hn, hnle, m, hm, I, f, D, a, b, c, u, H, ha, hab, hb, hδb, hI, hcov, hD, hvol, hu, hP,
    hT, hHm, hHsub, hdens, hreg, htrans, hslab, hdisj⟩ := hC
  have ha0 : 0 < a := lt_of_lt_of_le (pow_pos hδ 100) ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hb1 : b ≤ 1 := hb.trans (by norm_num)
  have hcnorm : ∀ j, ∀ i ∈ I j, ‖c j i‖ < 1 / 100 :=
    fun j i hi => asm_norm_lt ha0.le hb0.le (hP j i hi)
  -- an essentially distinct net of tubes in every cell
  have hnet := fun j => net_cover (I j) (hI j) ha0.le hab hb0 hb (c j) (u j) (hu j) (hcnorm j)
  choose M k F hM hk hF hFne hFdisj hFcard hFsub hhalf using hnet
  refine ⟨hn, hnle, m, hm, 4 * b, by positivity, ?_, ?_, M, f, D,
    fun j α => c j (k j α) - (1 / 2 : ℝ) • axisDir (u j (k j α)),
    fun j α => axisDir (u j (k j α)),
    fun j α => cTube b (c j (k j α)) (u j (k j α)) ∩ ⋃ i ∈ I j, H j i, F,
    hM, hD, hvol, ?_, ?_, ?_, ?_, ?_, ?_, hFne, hFdisj, ?_, ?_, ?_, ?_⟩
  · calc δ * δ ^ s ≤ δ * δ ^ (s / 16) := mul_le_mul_of_nonneg_left hss hδ.le
      _ ≤ b := hδb
      _ ≤ 4 * b := by linarith
  · linarith
  · exact fun j α => norm_axisDir (hu j _ (hk j α))
  · exact fun j α => cTube_subset_ball hb0.le (by linarith) (hu j _ (hk j α))
      (hcnorm j _ (hk j α))
  · exact fun j α β hαβ => hhalf j α β hαβ
  · exact fun j α => Metric.isOpen_thickening.measurableSet.inter
      (Finset.measurableSet_biUnion _ (hHm j))
  · exact fun j α => Set.inter_subset_left
  · -- density of the new shadings, from `cell_density`
    intro j α
    exact (ENNReal.ofReal_le_ofReal (asm_density_arith hδ ha hab hb1 hA2)).trans
      (hcell n (I j) a b (δ ^ (s / 16)) (c j) (u j) (H j) (k j α) ha0 hab hb hh0 hh1 (hu j)
        (hHm j) (fun i hi => (hHsub j i hi).trans Set.inter_subset_left)
        (fun i hi p hp => hreg j i hi p hp b hab hb1) (hk j α) (hdens j _ (hk j α)) (htrans j))
  · exact fun j α i hi => (hT j i (hF j α hi)).trans (Set.image_mono (hFsub j α i hi))
  · exact asm_coverage I F hA1 hcov hFcard
  · intro j ν s' r' hν hr'
    exact asm_slab (I j) (F j) _ _ _ hh0 hs0 (hF j) (hFsub j)
      (asm_cell_count hh0.le (Nat.cast_nonneg _) hA1 (hFcard j)) (hslab j ν s' r' hν hr')
  · exact asm_transport I f D H Y _ hvol
      (fun j α => Metric.isOpen_thickening.measurableSet.inter
        (Finset.measurableSet_biUnion _ (hHm j)))
      (fun j α => Set.inter_subset_right)
      (fun j i hi => (hHsub j i hi).trans Set.inter_subset_right) hdisj
