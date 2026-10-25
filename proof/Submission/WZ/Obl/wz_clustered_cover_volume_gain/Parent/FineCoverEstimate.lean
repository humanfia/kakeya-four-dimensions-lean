-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FineCoverEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FineScaleArithmetic
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverWeights

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open MeasureTheory Set Finset

/-- The balanced coarse cover bounds each complete fine fiber by the average. -/
theorem c_fiber_count_bound {δ h ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} (hδ : 0 < δ)
    (hC : C δ h n x v Y S Z ρ N y w f) (k : Fin N) :
    q {i | i ∈ S ∧ f i = k} * N ≤ δ ^ (-h) * n := by
  classical
  have hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      δ ^ (-h) * (S.filter (fun i => f i = k')).card := by
    intro k k'
    simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hC.2.2.2.2.2.2.1 k k'
  have hh := balanced_fiber_card_le S f hbal k
  simp only [Fintype.card_fin] at hh
  have hn : (S.card : ℝ) ≤ n := Nat.cast_le.mpr (by simpa using S.card_le_univ)
  have hbound := hh.trans (mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hδ.le _))
  simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hbound

/-- The fine-scale estimate of Section 9 on a complete selected fiber. Its
density exponent is left as an explicit hypothesis for later refinements. -/
theorem fine_multiplicity_of_cover {σ ω : ℝ} (hσ : 0 ≤ σ) (hR : R σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ δ ρ η h : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
      0 ≤ h → η ≤ h →
    ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (y w : Fin N → V) (f : Fin n → Fin N),
    A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
    ∀ k : Fin N,
      o (δ ^ η₀ * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
        ∑ i ∈ S with f i = k, μ (Z i) →
    ∀ M : ℝ, 0 ≤ M →
      (∀ p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
        M ≤ q {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) →
    M ≤ C₀ * δ ^ (-(ε + h)) * (δ / ρ) ^ (-ω) *
      (q {i | i ∈ S ∧ f i = k} * δ / ρ) ^ σ := by
  intro ε hε
  obtain ⟨C₀, hC₀, η₀, hη₀, hlocal⟩ := fiber_multiplicity_of_local_rescaling hR ε hε
  refine ⟨C₀, hC₀, η₀, hη₀, ?_⟩
  intro δ ρ η h hδ hδ100 hδρ hρ1 hh hη n N x v Y Z S y w f hA hC k hdense M hM hmult
  classical
  have hδ1 : δ ≤ 1 := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hpow : 1 ≤ δ ^ (-h) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hK : K δ (δ ^ (-h)) n x v := by
    intro W hW
    apply (hA.2.2.2.2.1 W hW).trans
    gcongr
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hne : (S.filter (fun i => f i = k)).Nonempty := by
    obtain ⟨i, hi, hik⟩ := c_fibers_nonempty hδ hA hC k
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hik⟩⟩
  have hdata : ∀ i ∈ S.filter (fun i => f i = k), ‖v i‖ = 1 ∧
      T δ (x i) (v i) ⊆ T ρ (y k) (w k) ∧ MeasurableSet (Z i) ∧
      Z i ⊆ T δ (x i) (v i) := by
    intro i hi
    obtain ⟨hiS, hik⟩ := Finset.mem_filter.mp hi
    refine ⟨(hA.2.1 i).1, ?_, (hC.1 i).1, (hC.1 i).2.1.trans (hA.2.1 i).2.2.2⟩
    simpa only [hik] using hC.2.2.2.1 i hiS
  have hcard : q {i | i ∈ S ∧ f i = k} = (S.filter (fun i => f i = k)).card := by
    simp only [q, ← Finset.coe_filter, Set.ncard_coe_finset]
  have hdense' : o (δ ^ η₀ * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
      ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by simpa only [hcard] using hdense
  have hmult' : ∀ p, (∃ i ∈ S.filter (fun i => f i = k), p ∈ Z i) →
      M ≤ q {i | i ∈ S.filter (fun i => f i = k) ∧ p ∈ Z i} := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := hp
    have hh := hmult p ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, hp⟩
    simpa only [Finset.mem_filter, and_assoc] using hh
  have hbound := hlocal δ ρ hδ hδ100 hδρ hρ1 (δ ^ (-h)) (δ ^ (-h)) hpow hpow
    n x v Z (y k) (w k) (S.filter (fun i => f i = k)) hne (hC.2.2.1 k)
    hdata hA.2.2.1 hdense' hK (below_slab_on_fiber hC.2.2.2.2.2.1 k) M hM hmult'
  rw [← hcard] at hbound
  have hu : 0 ≤ q {i | i ∈ S ∧ f i = k} * δ / ρ := by dsimp only [q]; positivity
  have herr := normalized_local_multiplicity_factor_le hδ hδ1 hu hh hσ
  have hmul := mul_le_mul_of_nonneg_left herr
    (by positivity : 0 ≤ C₀ * δ ^ (-ε) * (δ / ρ) ^ (-ω))
  have hbound' : M ≤ C₀ * δ ^ (-ε) * (δ / ρ) ^ (-ω) *
      (δ ^ (-h) * ((δ ^ (-h)) ^ (-(3 / 2 : ℝ)) * δ ^ (-h) *
        (q {i | i ∈ S ∧ f i = k} * δ / ρ)) ^ σ) := by
    simpa only [mul_assoc] using hbound
  refine hbound'.trans (hmul.trans_eq ?_)
  calc
    _ = C₀ * (δ ^ (-ε) * δ ^ (-h)) * (δ / ρ) ^ (-ω) *
        (q {i | i ∈ S ∧ f i = k} * δ / ρ) ^ σ := by ring
    _ = _ := by rw [← Real.rpow_add hδ, show -ε + -h = -(ε + h) by ring]

/-- The complete fine-scale bound (9.7), using a mass-comparable selected
coarse cover and the rich-cover count (9.6). -/
theorem fine_multiplicity_of_selected_rich_cover {σ ω : ℝ} (hσ : 0 ≤ σ) (hR : R σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ δ ρ θ η h τ ν a ζ J : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
      0 < θ → 0 < J → 0 ≤ h → η ≤ h → τ + η + ν + h ≤ η₀ →
    ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (y w : Fin N → V) (f : Fin n → Fin N),
    A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
    ∀ Q : Finset (Fin N), Q.Nonempty →
      δ ^ τ * (∑ i, (μ (Y i)).toReal) ≤ ∑ k ∈ Q, coarseWeight S Z f k →
      (∀ j ∈ Q, ∀ k ∈ Q, coarseWeight S Z f j ≤ δ ^ (-ν) * coarseWeight S Z f k) →
      δ ^ (a - ζ) * (θ / ρ) ^ 2 * J ≤ N →
    ∀ M : ℝ, 0 ≤ M →
      (∀ k ∈ Q, ∀ p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
        M ≤ q {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) →
    M ≤ C₀ * δ ^ (σ * ζ - ε - h - σ * (a + h)) * (δ / ρ) ^ (-ω) *
      ((n : ℝ) / J * δ * ρ / θ ^ 2) ^ σ := by
  intro ε hε
  obtain ⟨C₀, hC₀, η₀, hη₀, hlocal⟩ := fine_multiplicity_of_cover hσ hR ε hε
  refine ⟨C₀, hC₀, η₀, hη₀, ?_⟩
  intro δ ρ θ η h τ ν a ζ J hδ hδ100 hδρ hρ1 hθ hJ hh hη hbudget
    n N x v Y Z S y w f hA hC Q hQ hkeep hcmp hrich M hM hmult
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨k, hk⟩ := hQ
  have hdense := c_selected_fiber_density hδ hA hC Q hkeep hcmp k hk
  have hdense' : o (δ ^ η₀ * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
      ∑ i ∈ S with f i = k, μ (Z i) := by
    apply le_trans _ hdense
    apply ENNReal.ofReal_le_ofReal
    have hq : 0 ≤ q {i | i ∈ S ∧ f i = k} := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hbudget) hq)
      (sq_nonneg δ)
  have hbound := hlocal δ ρ η h hδ hδ100 hδρ hρ1 hh hη
    n N x v Y Z S y w f hA hC k hdense' M hM (hmult k hk)
  have hout := fine_multiplicity_of_rich_coarse_cover hδ (hδ.trans_le hδρ) hθ hJ
    (Nat.cast_nonneg n) (Nat.cast_nonneg (Set.ncard {i | i ∈ S ∧ f i = k}))
    hσ hC₀.le (c_fiber_count_bound hδ hC k) hrich hbound
  simpa only [show σ * ζ - (ε + h) - σ * (a + h) = σ * ζ - ε - h - σ * (a + h) by ring] using hout

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
