-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AngularAnnuli.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularSubfamily
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ScaleDyadic

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

/-- From a transverse incidence at each anchor point, choose one dyadic
angular annulus retaining a logarithmic share of anchor measure. -/
theorem transverse_annulus_selection {n : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (v : Fin n → V) (v₀ : V) (hv : ∀ i, ‖v i‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (H : Fin n → Set V) (A : Set V)
    (htrans : ∀ p ∈ A, ∃ i, p ∈ H i ∧ s ≤ pd (v i) v₀) :
    ∃ θ : ℝ, s / 2 ≤ θ ∧ θ ≤ 1 ∧ ∃ K : Finset (Fin n),
      (∀ i ∈ K, θ ≤ pd (v i) v₀ ∧ pd (v i) v₀ ≤ 2 * θ) ∧
      μ A ≤ ((Scale.dyExp 1 (s / 2) + 1 : ℕ) : ℝ≥0∞) * μ (A ∩ ⋃ i ∈ K, H i) := by
  classical
  let D : ℕ := Scale.dyExp 1 (s / 2) + 1
  let θ : Fin D → ℝ := fun j => 1 / (2 : ℝ) ^ (j : ℕ)
  let K : Fin D → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i => θ j ≤ pd (v i) v₀ ∧ pd (v i) v₀ ≤ 2 * θ j)
  let Y : Fin D → Set V := fun j => A ∩ ⋃ i ∈ K j, H i
  have hcover : A ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin D)), Y j := by
    intro p hp
    obtain ⟨i, hpi, hsi⟩ := htrans p hp
    have hp2 : pd (v i) v₀ ≤ 2 := by
      calc
        _ ≤ ‖v i - v₀‖ := min_le_left _ _
        _ ≤ ‖v i‖ + ‖v₀‖ := norm_sub_le _ _
        _ = 2 := by rw [hv i, hv₀]; norm_num
    obtain ⟨j, _, _, hlow, hhigh⟩ := Scale.dyadic_annulus hs hsi hp2
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_univ _, hp,
      mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow, hhigh⟩, hpi⟩⟩
  letI : Nonempty (Fin D) := ⟨⟨0, Nat.succ_pos _⟩⟩
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j : Fin D => μ (Y j))
    Finset.univ_nonempty
  refine ⟨θ j, ?_, ?_, K j, ?_, ?_⟩
  · calc
      s / 2 ≤ Scale.dyUp 1 (s / 2) := Scale.le_dyUp (by positivity) (by linarith)
      _ ≤ θ j := by
        dsimp [Scale.dyUp, θ]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ j.isLt)
  · exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · calc
      μ A ≤ ∑ k : Fin D, μ (Y k) := (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _k : Fin D, μ (Y j) := Finset.sum_le_sum fun k hk => hmax k hk
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, D, Y]

/-- Variable transverse angles still yield a thin filled neighbourhood at
some angle above half the prescribed lower bound. Only logarithmic losses
come from choosing the angular annulus. -/
theorem transverse_global_filling {n : ℕ} {a b h lam s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hlam : 0 < lam) (hs : 0 < s) (hs1 : s ≤ 1)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ : V) (u₀ : Fin 3 → V) (H₀ : Set V)
    (hu : ∀ i, Orthonormal ℝ (u i)) (hHm : ∀ i, MeasurableSet (H i))
    (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hH₀m : MeasurableSet H₀) (hH₀ : H₀ ⊆ prism a b c₀ u₀)
    (hdense₀ : O lam * μ (prism a b c₀ u₀) ≤ μ H₀)
    (htrans : ∀ p ∈ H₀, ∃ i, p ∈ H i ∧ s ≤ pd (u i 0) (u₀ 0)) :
    ∃ θ : ℝ, s / 2 ≤ θ ∧ θ ≤ 1 ∧
      O ((lam / (Scale.dyExp 1 (s / 2) + 1 : ℕ) / 16000) ^ 2 * h ^ 2 * θ * b ^ 2 /
        (52428800000000 * (257 ^ 4 : ℕ) * (1 + Real.log (b / a)))) ≤
        μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + 2 * θ * b} ∩
          (cTube b c₀ u₀ ∩ ⋃ i, H i)) := by
  classical
  have hb0 : 0 < b := ha.trans_le hab
  obtain ⟨θ, hsθ, hθ1, K, hangle, hretain⟩ := transverse_annulus_selection hs hs1
    (fun i => u i 0) (u₀ 0) (fun i => (hu i).1 0) (hu₀.1 0) H H₀ htrans
  let D : ℝ := (Scale.dyExp 1 (s / 2) + 1 : ℕ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hθ : 0 < θ := (half_pos hs).trans_le hsθ
  let A : Set V := H₀ ∩ ⋃ i ∈ K, H i
  have hAm : MeasurableSet A := hH₀m.inter (Finset.measurableSet_biUnion K (fun i _ => hHm i))
  have hretain' : μ H₀ ≤ O D * μ A := by
    simpa only [D, O, ENNReal.ofReal_natCast] using hretain
  have hdense : O (lam / D) * μ (prism a b c₀ u₀) ≤ μ A := by
    have hmul : O D * (O (lam / D) * μ (prism a b c₀ u₀)) ≤ O D * μ A := by
      calc
        _ = O lam * μ (prism a b c₀ u₀) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hD.le]
          congr 2
          field_simp
        _ ≤ μ H₀ := hdense₀
        _ ≤ _ := hretain'
    have hD0 : O D ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hD)
    have ht := mul_le_mul' (le_refl (O D)⁻¹) hmul
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hD0 ENNReal.ofReal_ne_top, one_mul] using ht
  have hApos : μ A ≠ 0 := by
    apply ne_of_gt
    apply lt_of_lt_of_le _ hdense
    apply pos_iff_ne_zero.mpr
    apply mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos hlam hD)))
    apply ne_of_gt
    change 0 < volume (prism a b c₀ u₀)
    rw [volume_prism ha.le (ha.le.trans hab) c₀ hu₀]
    apply ENNReal.ofReal_pos.mpr
    positivity
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hApos
  obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp hp.2
  refine ⟨θ, hsθ, hθ1, ?_⟩
  have hf := angular_global_filling_subfamily (B := 2) (by norm_num) ha hab hb hh
    (div_pos hlam hD) hθ hθ1 c u H c₀ u₀ A K ⟨i, hi⟩
    (fun i _ => hu i) (fun i _ => hHm i) (fun i _ => hHU i) (fun i _ => hregular i)
    hu₀ hAm (inter_subset_left.trans hH₀) hdense inter_subset_right (by simpa using hangle)
  convert hf using 1 <;> norm_num [D]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
