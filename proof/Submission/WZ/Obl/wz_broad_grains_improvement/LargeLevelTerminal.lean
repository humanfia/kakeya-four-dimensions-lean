-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.LargeLevelTerminal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.MultiplicityCount
import Submission.WZ.Obl.wz_broad_grains_improvement.NonemptyGrains
import Submission.WZ.Obl.wz_broad_grains_improvement.CommonCut

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- A sufficiently large product of grain length squared and fibre multiplicity
gives the terminal local count. Dense pruning keeps a quarter of the fine mass,
and all coarse carriers and both geometric scales remain unchanged. -/
theorem stage_three_of_large_grain_level
    {ω ζ δ h h' ρ a c g m mK : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {G : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h')
    (hbudget : 4 * δ ^ h' ≤ δ ^ h) (h4 : 4 * δ ≤ c)
    (hm : 0 < m) (hmK : 0 ≤ mK)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hK : K δ mK n x v) (hC : C δ h n x v Y S Z ρ N y w f True)
    (hH : HB δ h n x v S Z ρ N y w f a c 0 g L z e G γ m)
    (hρlow : δ ^ (1 - ω / 100) ≤ ρ) (hρup : ρ ≤ δ ^ (ω / 100))
    (hlen : δ ^ ζ * (ρ / δ) * N / n ≤ c)
    (hbr : ∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i})
    (hlarge : 3981312000 * mK / (m * (δ ^ h / 2) * c ^ 2) ≤ δ ^ (-ζ)) :
    J ω ζ δ h' ρ c n x v Y 3 := by
  classical
  have hpow : 0 < δ ^ h' := Real.rpow_pos_of_pos hδ _
  have hhalf : δ ^ h' ≤ δ ^ h / 2 := by linarith
  obtain ⟨G', hGsub, hGdense, hZm, hretain, hH'⟩ := dense_cut hδ hhalf hC.1 hH
  let R := wz_clustered_cover_volume_gain.assignedFiber γ G'
  let Z' : Fin n → Set V := fun i => Z i ∩ R (f i)
  have hG'm (j : Fin L) : M (G' j) := (hH'.2.2.2.2.1 j).1
  have hRm (k : Fin N) : M (R k) :=
    wz_clustered_cover_volume_gain.measurable_assignedFiber γ hG'm k
  have hC' : C δ h' n x v Y S Z' ρ N y w f True :=
    cover_common_cut hδ hδ1 hh (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hC R hRm hretain (by linarith)
  have hZ' (i : Fin n) : M (Z' i) ∧ Z' i ⊆ T δ (x i) (v i) ∧ (i ∉ S → Z' i = ∅) :=
    ⟨(hC'.1 i).1, ((hC'.1 i).2.1).trans (hY i), (hC'.1 i).2.2⟩
  have ha : 0 ≤ a := hδ.le.trans hH.1
  have hrc : 0 ≤ ρ * c := ha.trans hH.2.1
  have hc : 0 ≤ c := hrc.trans hH.2.2.1
  let Q₀ := Finset.univ.filter (fun j => G' j ≠ ∅)
  have hdense (j : Fin L) (hj : j ∈ Q₀) :
      O ((δ ^ h / 2) * (a * (ρ * c) * c)) ≤ μ (G' j) := by
    have hd := hGdense j (Finset.mem_filter.mp hj).2
    rw [show μ (P a (ρ * c) c (z j) (e j)) = O (a * (ρ * c) * c) from
      wz_clustered_cover_volume_gain.frozen_prism_volume ha hrc hc _ _,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ h / 2)] at hd
    exact hd
  have hlocal := local_grain_count_of_katz_tao hδ h4 hm
    (by positivity : 0 < δ ^ h / 2) hmK hv hK hZ' hH' Q₀ hdense
  have hHfin : H δ h' n x v S Z' ρ N y w f a c 0 (δ ^ (-ζ)) := by
    apply grains_of_nonempty_count hδ hH'
    intro j W hW
    apply le_trans (b := O (3981312000 * mK / (m * (δ ^ h / 2) * c ^ 2)) * μ W)
    · simpa only [Q₀, Finset.mem_filter, Finset.mem_univ, true_and] using hlocal j W hW
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal hlarge) le_rfl
  refine ⟨S, Z', N, y, w, f, a, δ ^ (-ζ), hC', hρlow,
    Real.rpow_pos_of_pos hδ _, ?_, hHfin,
    fun _ => hlen, fun _ => hρup, fun _ => le_rfl⟩
  exact broad_fibre_common_cut hδ hδ1 hh hbr R

end WangZahlLot.Obl.wz_broad_grains_improvement
