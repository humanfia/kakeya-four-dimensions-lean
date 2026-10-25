-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CappedParameterCell.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.ParameterCell
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.EndpointPairs
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedPieces
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedEndpoint
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.InputMass

/- Adapted from this workspace: o197/x0567, 422e78fd8000, CappedParameterCell.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P T I A bodyCount)

/-- Endpoint-pair pruning and one fixed parameter class preserve capped
valid data, with uniform constant losses independent of the family size. -/
theorem capped_parameter_cell {θ : ℝ} (hθ : 0 < θ) :
    ∃ q : ℝ, 0 < q ∧ ∀ {ω ζ δ h h₁ h₂ ρ c R : ℝ} {n : ℕ}
      (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V},
      0 < δ → δ ≤ 1 → δ ≤ θ / 8 → h ≤ h₁ → h₁ ≤ h₂ → 0 ≤ R →
      4608 * (R + 2 * c) ≤ δ ^ (2 * h) →
      O (δ ^ h₁) ≤ O (q / 4) * O (δ ^ h) →
      δ ^ (-h₁) ≤ (q / 2) * δ ^ (-h₂) →
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      D.Valid ω ζ δ h ρ c x v Y 1 → D.HasCaps δ h ρ c →
      ∃ (D' : PrismData n) (y u : V), D'.a = D.a ∧ ‖u‖ = 1 ∧
        D'.Valid ω ζ δ h₂ ρ c x v Y 1 ∧ D'.HasCaps δ h₂ ρ c ∧
        ∀ i j, (D'.W i j).Nonempty →
          ‖v i - u‖ ≤ θ / 100 ∧ T δ (x i) (v i) ⊆ T (θ / 4) y u ∧
          D'.PairAway ρ c R x v i j := by
  obtain ⟨N, hN, hclasses⟩ := exists_parameter_classes hθ
  let q : ℝ := 1 / (2 * N)
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q, hq, ?_⟩
  intro ω ζ δ h h₁ h₂ ρ c R n D x v Y hδ hδ1 hδθ hh₁ hh₂ hR hbudget hmassbudget hbroad hA H Hcap
  have hx (i : Fin n) : ‖x i‖ ≤ 1 := by
    apply (mem_ball_zero_iff.mp ((hA.2.1 i).2.1 ?_)).le
    exact mem_thickening_iff.mpr ⟨x i, left_mem_segment ℝ _ _, by simpa using hδ⟩
  obtain ⟨f, hf⟩ := hclasses x v hx (fun i => (hA.2.1 i).1)
  let w (i : Fin n) := ∑ j ∈ Finset.univ.filter (fun j => D.PairAway ρ c R x v i j), volume (D.W i j)
  have hhalf := endpoint_pair_mass_fraction D hδ hR hbudget hA H
  have hYpos : 0 < ∑ i, volume (Y i) :=
    WangZahlLot.Obl.wz_move_two_dense_broad_prisms.admissible_mass_pos hδ hA
  have hMpos : 0 < ∑ i, ∑ j, volume (D.W i j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne' hYpos.ne').trans_le
      H.2.2.2.2.2.1
  have hwpos : 0 < ∑ i, w i :=
    (ENNReal.mul_pos (by norm_num : (1 / 2 : ENNReal) ≠ 0) hMpos.ne').trans_le hhalf
  obtain ⟨i₀, _, hi₀⟩ := massful_parameter_class hN f w hwpos
  let Z := fun i j => if f i = f i₀ then
    (if D.PairAway ρ c R x v i j then D.W i j else ∅) else ∅
  have hZ (i : Fin n) (j : Fin D.L) : MeasurableSet (Z i j) ∧ Z i j ⊆ D.W i j := by
    dsimp [Z]
    split_ifs
    · exact ⟨(H.2.2.2.2.1 i j).1, Subset.rfl⟩
    · exact ⟨MeasurableSet.empty, empty_subset _⟩
    · exact ⟨MeasurableSet.empty, empty_subset _⟩
  have hsum : ∑ i, ∑ j, volume (Z i j) = ∑ i ∈ Finset.univ.filter (fun i => f i = f i₀), w i := by
    simp only [Z, Finset.sum_filter, apply_ite volume, measure_empty]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f i = f i₀ <;> simp [hi, w, Finset.sum_filter]
  have hqeq : O q = (N : ENNReal)⁻¹ * (1 / 2 : ENNReal) := by
    change ENNReal.ofReal (1 / (2 * (N : ℝ))) = _
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * N),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [one_div, ENNReal.mul_inv, mul_comm]
  have hretain : O q * (∑ i, ∑ j, volume (D.W i j)) ≤ ∑ i, ∑ j, volume (Z i j) := by
    rw [hsum, hqeq, mul_assoc]
    exact (mul_le_mul' le_rfl hhalf).trans hi₀
  have hdensity : O (δ ^ h₂) ≤ O (q * δ ^ h / 4) := by
    calc
      _ ≤ O (δ ^ h₁) := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hh₂)
      _ ≤ O (q / 4) * O (δ ^ h) := hmassbudget
      _ = _ := by
        change ENNReal.ofReal _ * ENNReal.ofReal _ = ENNReal.ofReal _
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q / 4)]
        congr 1
        ring
  obtain ⟨m, hm, hcount, havg⟩ := Hcap
  obtain ⟨L, g, U, hg, hU, HU, hcountU, havgU⟩ := select_capped_pieces D hδ hδ1 hh₁ hh₂
    (Real.rpow_pos_of_pos hδ h) hq hmassbudget hdensity hbroad H
    (fun i => (hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1) m hm hcount havg Z hZ hretain
  let D' := (D.select D.s g id (D.γ ∘ g)).refinePieces U
  refine ⟨D', x i₀, v i₀, rfl, (hA.2.1 i₀).1, HU, ?_, ?_⟩
  · refine ⟨m ∘ g, fun j => hm (g j), hcountU, ?_⟩
    intro j
    have hb : O (δ ^ h₂ * m (g j)) ≤ O ((q * δ ^ h / 4) * m (g j)) := by
      change ENNReal.ofReal _ ≤ ENNReal.ofReal _
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
        ENNReal.ofReal_mul (by positivity : 0 ≤ q * δ ^ h / 4)]
      exact mul_le_mul' hdensity le_rfl
    exact (mul_le_mul' hb le_rfl).trans (havgU j)
  · intro i j hne
    obtain ⟨p, hp⟩ := hne
    have hz := (hU i j).2 hp
    have hfi : f i = f i₀ := by
      by_contra hn
      simpa only [Z, hn, if_false, mem_empty_iff_false] using hz
    have haway : D.PairAway ρ c R x v i (g j) := by
      by_contra hn
      simpa only [Z, hfi, if_true, hn, if_false, mem_empty_iff_false] using hz
    exact ⟨(hf i i₀ hfi).1, (hf i i₀ hfi).2 δ hδθ, haway⟩

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
