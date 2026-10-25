-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoarseCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoarseShading
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BalancedSlab

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open Finset MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

/-- The length-eight carrier of a factoring box and its coarse shading. -/
def factoringCarrier (b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  Carrier 8 (3 * b) (z - (1 / 2 : ℝ) • e.symm (EuclideanSpace.single 2 1))
    (e.symm (EuclideanSpace.single 2 1))

theorem box_subset_factoringCarrier {a b : ℝ} (hab : a ≤ b) (hb : 0 < b)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Factor.box a b 8 z e ⊆ factoringCarrier b z e := by
  refine (box_subset_carrier hab hb (by norm_num) z e (e.apply_symm_apply _)).trans ?_
  exact thickening_mono (by linarith : 2 * b ≤ 3 * b) _

namespace Interfaces

/-- The actual selected factorization transfers the fine slab count to its coarse carriers. -/
theorem factored_carrier_slab_count {δ η h ρ K m a b D : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hU : U.Nonempty)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hcover : Factor.AssignedCover 4 ρ K y w U m a b L z e g)
    (hcard : (n : ℝ) ≤ D * (S.filter fun i => f i ∈ U).card) :
    ∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      o (q {j | factoringCarrier b (z j) (e j) ⊆ {p | |inner ℝ u p - t| ≤ r}}) ≤
        o (δ ^ (-h) * K * D * δ ^ (-η) * L) * μ (I ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  classical
  have hb : 0 < b := hδ.trans_le (hδρ.trans (hcover.width.trans hcover.ordered))
  obtain ⟨k, hk⟩ := hU
  obtain ⟨i, hiS, hfi⟩ := c_fibers_nonempty hδ hA hC k
  have hSel : (S.filter fun i => f i ∈ U).Nonempty :=
    ⟨i, mem_filter.mpr ⟨hiS, by simpa only [hfi] using hk⟩⟩
  have hf : ∀ k k', ((S.filter fun i => f i = k).card : ℝ) ≤
      δ ^ (-h) * (S.filter fun i => f i = k').card := by
    intro k k'
    simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hC.2.2.2.2.2.2.1 k k'
  have hbal := balanced_selected_assignment_comp S U ⟨k, hk⟩ f g
    (Real.rpow_nonneg hδ.le _) hK hf hcover.balanced
  apply slab_count_of_balanced_cover (S.filter fun i => f i ∈ U) hSel (g ∘ f)
    (fun j => factoringCarrier b (z j) (e j)) (mul_nonneg (Real.rpow_nonneg hδ.le _) hK)
    hD (Real.rpow_nonneg hδ.le _) (fun i hi => (hA.2.1 i).2.1) ?_ hbal hcard hA.2.2.2.2.2
  intro i hi
  obtain ⟨hiS, hiU⟩ := mem_filter.mp hi
  have hbox : T ρ (y (f i)) (w (f i)) ⊆ Factor.box a b 8 (z (g (f i))) (e (g (f i))) := by
    simpa only [T, Factor.tube, show (2 : ℝ) * 4 = 8 by norm_num] using hcover.covers (f i) hiU
  exact (hC.2.2.2.1 i hiS).trans
    (hbox.trans (box_subset_factoringCarrier hcover.ordered hb _ _))

/-- Enlarging almost-round factoring boxes gives the coarse convex count with its exact loss. -/
theorem factored_carrier_katz_count {ρ K m a b : ℝ} {N L : ℕ}
    {y w : Fin N → V} {U : Finset (Fin N)} {z : Fin L → V}
    {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hcover : Factor.AssignedCover 4 ρ K y w U m a b L z e g) :
    ∀ W, Convex ℝ W →
      o (q {j | factoringCarrier b (z j) (e j) ⊆ W} * (3 * b) ^ 2) ≤
        o ((9 * b / (8 * a)) * K) * μ W := by
  classical
  intro W hW
  have ha : 0 < a := hρ.trans_le hcover.width
  have hb : 0 < b := ha.trans_le hcover.ordered
  let B := univ.filter fun j => factoringCarrier b (z j) (e j) ⊆ W
  let Q := univ.filter fun j => Factor.box a b 8 (z j) (e j) ⊆ W
  have hc : B.card ≤ Q.card := card_le_card fun j hj =>
    mem_filter.mpr ⟨mem_univ _, (box_subset_factoringCarrier hcover.ordered hb _ _).trans
      (mem_filter.mp hj).2⟩
  have hh : o ((B.card : ℝ) * (a * b * 8)) ≤ o K * μ W := by
    refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hc) (by positivity))).trans ?_
    simpa only [Q, o, μ, show (2 : ℝ) * 4 = 8 by norm_num] using hcover.above W hW
  have hq : q {j | factoringCarrier b (z j) (e j) ⊆ W} = (B.card : ℝ) := by
    have he : {j | factoringCarrier b (z j) (e j) ⊆ W} = (B : Set (Fin L)) := by
      ext j
      simp [B]
    simp only [q, he, Set.ncard_coe_finset]
  rw [hq]
  calc
    _ = o (9 * b / (8 * a)) * o ((B.card : ℝ) * (a * b * 8)) := by
      rw [o, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    _ ≤ o (9 * b / (8 * a)) * (o K * μ W) := mul_le_mul_right hh _
    _ = _ := by rw [← mul_assoc, o, ← ENNReal.ofReal_mul (by positivity)]

end Interfaces

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
