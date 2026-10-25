-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.NativeGeometry; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.GridCalibration
import Submission.Lib.K4AffineMeshCaps.Transport

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory MvPolynomial Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem measurableSet_predictorEvent (hbase : p.Basic) {k : ℕ} {s v ε R : ℝ}
    (hat : p.AtDepth k s R) (i : Fin (p.n k s)) (G : MvPolynomial (Fin 3) ℝ) :
    MeasurableSet (p.PredictorEvent k s v ε i G) := by
  let J := block (p.T k s) (p.j k s i)
  let V : Set (Fin 6 → ℝ) := {a | ∀ t ∈ J,
    |eval (Submission.Lib.K4ContactNormalization.point a t) (p.P k) -
      eval (Submission.Lib.K4ContactNormalization.point a t ∘ Fin.castSucc) G| ≤
        p.N k ^ ε * p.N k ^ (-s - v)}
  have hV : IsClosed V := by
    dsimp [V]
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro _ht
    apply isClosed_le _ continuous_const
    have hx : Continuous (fun a : Fin 6 → ℝ =>
        Submission.Lib.K4ContactNormalization.point a t) := by
      unfold Submission.Lib.K4ContactNormalization.point
      fun_prop
    exact ((p.P k).continuous_eval.comp hx |>.sub
      (G.continuous_eval.comp (by fun_prop))).abs
  have hB : MeasurableSet (p.B k s i) := (hat.2.2.1 i).2.1
  have heq : p.PredictorEvent k s v ε i G =
      (p.B k s i ∩ (p.b k ⁻¹' V)) ×ˢ J := by
    ext ω
    change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
    tauto
  rw [heq]
  exact (hB.inter ((hbase k).1 hV.measurableSet)).prod measurableSet_Icc

/-- Actual assignment geometry bounds the original base, including on
trajectories of zero prior mass. -/
theorem AtDepth.base_bound {k : ℕ} {s R : ℝ} (hat : p.AtDepth k s R)
    (hN : 2 ≤ p.N k) (hK : 1 ≤ p.K k) (hℓ : 0 < p.ℓ) (hs : 0 ≤ s)
    (i : Fin (p.n k s)) {l : α} (hl : l ∈ p.B k s i)
    {t : ℝ} (ht : t ∈ block (p.T k s) (p.j k s i)) :
    ∀ j : Fin 3, |(p.x k l t ∘ Fin.castSucc) j| ≤ 6 * p.K k ^ 2 := by
  let q := (2 : ℝ) ^ (-(p.T k s : ℤ))
  let g := p.N k ^ (-p.ℓ * s)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hg0 : 0 ≤ g := Real.rpow_nonneg (by linarith) _
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by nlinarith)
  have ht1 := Submission.Obl.k4_balanced_native_packet_transport.Pullback.block_subset_unit
    (p.j k s i) ht
  have htA : |t| ≤ 1 := by rw [abs_of_nonneg ht1.1]; exact ht1.2
  have hrow := hat.2.2.2.2.1 i
  have hc := hrow.2.2.2.1
  have hgeo := hrow.2.2.2.2.2.1 l ((hat.2.2.1 i).2.2 hl) t ht
  have hZerr : |(p.x k l t) 1 - p.c k s i 0 - t * p.c k s i 1| ≤ p.K k := by
    exact hgeo.1.trans (mul_le_of_le_one_right (by linarith) hq1)
  have hYerr : |(p.x k l t) 2 - p.c k s i 2 - t * p.c k s i 3 -
      p.c k s i 4 * (p.x k l t) 1| ≤ p.K k := by
    apply hgeo.2.1.trans
    calc
      p.K k * q * g ≤ p.K k * 1 * 1 := by gcongr
      _ = p.K k := by ring
  have hZ : |(p.x k l t) 1| ≤ 3 * p.K k := by
    calc
      _ = |((p.x k l t) 1 - p.c k s i 0 - t * p.c k s i 1) +
        p.c k s i 0 + t * p.c k s i 1| := by congr 1; ring
      _ ≤ |(p.x k l t) 1 - p.c k s i 0 - t * p.c k s i 1| +
        |p.c k s i 0| + |t * p.c k s i 1| := abs_add_three _ _ _
      _ ≤ p.K k + p.K k + 1 * p.K k := by
        apply add_le_add (add_le_add hZerr (hc 0))
        rw [abs_mul]
        exact mul_le_mul htA (hc 1) (abs_nonneg _) (by norm_num)
      _ = 3 * p.K k := by ring
  have hY : |(p.x k l t) 2| ≤ 6 * p.K k ^ 2 := by
    have hsum := abs_add_le ( (p.x k l t) 2 - p.c k s i 2 - t * p.c k s i 3 -
      p.c k s i 4 * (p.x k l t) 1) (p.c k s i 2 + t * p.c k s i 3 +
        p.c k s i 4 * (p.x k l t) 1)
    have hsum2 := abs_add_three (p.c k s i 2) (t * p.c k s i 3)
      (p.c k s i 4 * (p.x k l t) 1)
    have htprod : |t * p.c k s i 3| ≤ p.K k := by
      rw [abs_mul]
      simpa using mul_le_mul htA (hc 3) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hcp : |p.c k s i 4 * (p.x k l t) 1| ≤ 3 * p.K k ^ 2 := by
      rw [abs_mul]
      calc
        _ ≤ p.K k * (3 * p.K k) := mul_le_mul (hc 4) hZ (abs_nonneg _) (by linarith)
        _ = _ := by ring
    have hK2 : p.K k ≤ p.K k ^ 2 := by nlinarith
    have htotal : |(p.x k l t) 2| ≤ p.K k + (p.K k + p.K k + 3 * p.K k ^ 2) := by
      convert le_trans hsum (add_le_add hYerr (hsum2.trans
        (add_le_add (add_le_add (hc 2) htprod) hcp))) using 1 <;> congr 1 <;> ring
    exact htotal.trans (by nlinarith)
  intro j
  fin_cases j
  · change |t| ≤ _
    nlinarith [sq_nonneg (p.K k - 1)]
  · exact hZ.trans (by nlinarith)
  · exact hY

/-- Bounded native signal and its primitive unit-signal caps imply a pure
base mesh ceiling. -/
theorem native_base_cell_cap (hbase : p.Basic) {k : ℕ} {r : ℝ}
    (hN : 2 ≤ p.N k) (hK : 1 ≤ p.K k)
    (hcap : ∀ (q : Fin 3 → ℤ) (a : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k)⌋ = a} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-r)) ^ 3)) (q : Fin 3 → ℤ) :
    p.μ k {ω | Submission.Lib.K4CommonLocalChoice.cell (p.N k ^ (-r))
      (p.x k ω.1 ω.2 ∘ Fin.castSucc) = q} ≤
      ENNReal.ofReal (6 * p.K k ^ 2 * (p.N k ^ (-r)) ^ 3) := by
  have hg := hbase k
  have hsupp : ∀ᵐ ω ∂p.μ k, ω ∈ univ ×ˢ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hg.2.2.2.2.2.1
  have hbound : ∀ᵐ ω ∂p.μ k, True → |eval (p.x k ω.1 ω.2) (p.P k)| ≤ p.K k := by
    filter_upwards [hsupp, hg.2.2.2.2.2.2.2.2.2] with ω ht hh
    exact fun _ => (hh.1 ω.2 ht.2).1
  have hz : (fun ω : α × ℝ => Submission.Lib.K4AffineMeshCaps.baseMesh
      (p.N k ^ (-r)) (p.x k ω.1 ω.2 ∘ Fin.castSucc)) = p.z k (p.N k) r := by
    funext ω j
    fin_cases j <;> rfl
  have h := Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal
    (p.μ k) (fun ω => p.x k ω.1 ω.2 ∘ Fin.castSucc)
    (fun ω => eval (p.x k ω.1 ω.2) (p.P k)) (fun _ => True)
    (delta := p.N k ^ (-r)) (a := 1) (L := p.K k) (C := p.K k)
    (Real.rpow_pos_of_pos (by linarith) _) (by norm_num) (by linarith) (by linarith)
    hbound (fun q a => by simpa only [← hz, div_one, and_true] using hcap q a) q
  change p.μ k {ω | Submission.Lib.K4CommonLocalChoice.cell (p.N k ^ (-r))
    (p.x k ω.1 ω.2 ∘ Fin.castSucc) = q ∧ True} ≤ _ at h
  apply le_trans (by simpa only [and_true] using h)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simp only [div_one]
  nlinarith

end Parent
end
end Submission.Obl.k4_general_compared_layers_velocity_lists
