/-
Adapted from: here:o018
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib

/-!
The countable-grid compactness step in Lemma `a01:homogenization`. Bounds hold
on one common subsequence, and fixed-pair inequalities may become valid at
different stages. Their errors disappear in the limiting exponent profile.
-/

open Set Filter
open scoped Topology NNReal

namespace Submission.Lib.K4Homogenization

/-- Bounded exponent tables admit one subsequence converging at every tested depth. -/
theorem bounded_profile_subsequence {ι : Type*} [Countable ι]
    (p : ℕ → ι → ℝ) (M : ℝ) (hp : ∀ n i, |p n i| ≤ M) :
    ∃ (f : ι → ℝ) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ i, Tendsto (fun n => p (ψ n) i) atTop (𝓝 (f i))) ∧
      ∀ i, |f i| ≤ M := by
  have hcompact : IsCompact {q : ι → ℝ | ∀ i, q i ∈ Icc (-M) M} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  have hp' : ∀ n, p n ∈ {q : ι → ℝ | ∀ i, q i ∈ Icc (-M) M} :=
    fun n i => abs_le.mp (hp n i)
  obtain ⟨f, hf, ψ, hψ, hlim⟩ := hcompact.tendsto_subseq hp'
  exact ⟨f, ψ, hψ, tendsto_pi_nhds.mp hlim, fun i => abs_le.mpr (hf i)⟩

/-- Every fixed-pair inequality survives a common subsequential limit when its defect
tends to zero. No uniform starting stage over the countable set of pairs is required. -/
theorem profile_relations_subsequence {ι : Type*} [Countable ι]
    (p : ℕ → ι → ℝ) (M : ℝ) (hp : ∀ n i, |p n i| ≤ M)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (lower upper : ι → ι → ℝ)
    (hrel : ∀ i j, ∀ᶠ n in atTop,
      lower i j - error n ≤ p n j - p n i ∧
        p n j - p n i ≤ upper i j + error n) :
    ∃ (f : ι → ℝ) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ i, Tendsto (fun n => p (ψ n) i) atTop (𝓝 (f i))) ∧
      (∀ i, |f i| ≤ M) ∧
      ∀ i j, lower i j ≤ f j - f i ∧ f j - f i ≤ upper i j := by
  obtain ⟨f, ψ, hψ, hlim, hf⟩ := bounded_profile_subsequence p M hp
  refine ⟨f, ψ, hψ, hlim, hf, ?_⟩
  intro i j
  have hdiff := (hlim j).sub (hlim i)
  have herr := herror.comp hψ.tendsto_atTop
  have hrel' := hψ.tendsto_atTop.eventually (hrel i j)
  constructor
  · have hlow := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub herr) hdiff
      (hrel'.mono fun n hn => hn.1)
    simpa only [sub_zero] using hlow
  · have hupp := le_of_tendsto_of_tendsto hdiff (tendsto_const_nhds.add herr)
      (hrel'.mono fun n hn => hn.2)
    simpa only [add_zero] using hupp

/-- Approximate Lipschitz bounds of a countable exponent table yield an exact limiting bound. -/
theorem profile_lipschitz_subsequence {ι X : Type*} [Countable ι] [PseudoMetricSpace X]
    (x : ι → X) (p : ℕ → ι → ℝ) (M : ℝ) (hp : ∀ n i, |p n i| ≤ M)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0)) (K : ℝ≥0)
    (hLip : ∀ i j, ∀ᶠ n in atTop, |p n j - p n i| ≤ (K : ℝ) * dist (x i) (x j) + error n) :
    ∃ (f : ι → ℝ) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ i, Tendsto (fun n => p (ψ n) i) atTop (𝓝 (f i))) ∧
      (∀ i, |f i| ≤ M) ∧
      ∀ i j, |f j - f i| ≤ (K : ℝ) * dist (x i) (x j) := by
  obtain ⟨f, ψ, hψ, hlim, hf, hrel⟩ := profile_relations_subsequence p M hp error herror
    (fun i j => -((K : ℝ) * dist (x i) (x j)))
    (fun i j => (K : ℝ) * dist (x i) (x j)) (by
      intro i j
      filter_upwards [hLip i j] with n hn
      rcases abs_le.mp hn with ⟨hlo, hhi⟩
      exact ⟨by linarith, hhi⟩)
  exact ⟨f, ψ, hψ, hlim, hf, fun i j => abs_le.mpr (hrel i j)⟩

/-- The limiting table extends to a Lipschitz profile on the ambient depth space. The map
enumerating tested depths may repeat points; the limit is consistent on every fiber. -/
theorem countable_lipschitz_profile_subsequence {ι X : Type*}
    [Countable ι] [PseudoMetricSpace X] (x : ι → X)
    (p : ℕ → ι → ℝ) (M : ℝ) (hp : ∀ n i, |p n i| ≤ M)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0)) (K : ℝ≥0)
    (hLip : ∀ i j, ∀ᶠ n in atTop, |p n j - p n i| ≤ (K : ℝ) * dist (x i) (x j) + error n) :
    ∃ F : X → ℝ, LipschitzWith K F ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (∀ i, Tendsto (fun n => p (ψ n) i) atTop (𝓝 (F (x i)))) ∧
      ∀ i, |F (x i)| ≤ M := by
  classical
  obtain ⟨f, ψ, hψ, hlim, hf, hbound⟩ :=
    profile_lipschitz_subsequence x p M hp error herror K hLip
  have hfiber (i j : ι) (hij : x i = x j) : f i = f j := by
    have h := hbound j i
    rw [hij, dist_self, mul_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  let f₀ : X → ℝ := fun z => if hz : z ∈ Set.range x then f (Classical.choose hz) else 0
  have hf₀ (i : ι) : f₀ (x i) = f i := by
    have hi : x i ∈ Set.range x := mem_range_self i
    simp only [f₀, dite_eq_left hi]
    exact hfiber _ _ (Classical.choose_spec hi)
  have hLip₀ : LipschitzOnWith K f₀ (Set.range x) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [hf₀ i, hf₀ j, Real.dist_eq]
    simpa only [abs_sub_comm] using hbound i j
  obtain ⟨F, hF, hEq⟩ := _root_.LipschitzOnWith.extend_real hLip₀
  have hFi (i : ι) : F (x i) = f i := (hEq (mem_range_self i)).symm.trans (hf₀ i)
  refine ⟨F, hF, ψ, hψ, ?_, ?_⟩
  · intro i
    simpa only [hFi i] using hlim i
  · intro i
    simpa only [hFi i] using hf i

/-- Once a continuous profile is available, monotonicity and one-sided Lipschitz bounds
on rational depths determine the same bounds at every real depth. -/
theorem real_profile_bounds_of_rational {F : ℝ → ℝ} (hF : Continuous F) (K : ℝ)
    (hQ : ∀ a b : ℚ, a ≤ b →
      0 ≤ F (b : ℝ) - F (a : ℝ) ∧ F (b : ℝ) - F (a : ℝ) ≤ K * ((b : ℝ) - a)) :
    ∀ x y : ℝ, x ≤ y → 0 ≤ F y - F x ∧ F y - F x ≤ K * (y - x) := by
  have hclosed : IsClosed {p : ℝ × ℝ | F p.1 - F p.2 ≤ K * max (p.1 - p.2) 0} :=
    isClosed_le ((hF.comp continuous_fst).sub (hF.comp continuous_snd))
      (continuous_const.mul ((continuous_fst.sub continuous_snd).max continuous_const))
  have hrel : ∀ x y : ℝ, F x - F y ≤ K * max (x - y) 0 := by
    intro x y
    refine Rat.denseRange_cast.induction_on₂ hclosed ?_ x y
    intro a b
    by_cases hab : a ≤ b
    · have hab' : (a : ℝ) - b ≤ 0 := by exact_mod_cast sub_nonpos.mpr hab
      rw [max_eq_right hab', mul_zero]
      linarith [(hQ a b hab).1]
    · have hba : b ≤ a := (lt_of_not_ge hab).le
      have hba' : (0 : ℝ) ≤ (a : ℝ) - b := by exact_mod_cast sub_nonneg.mpr hba
      rw [max_eq_left hba']
      exact (hQ b a hba).2
  intro x y hxy
  have hlo := hrel x y
  have hhi := hrel y x
  rw [max_eq_right (sub_nonpos.mpr hxy), mul_zero] at hlo
  rw [max_eq_left (sub_nonneg.mpr hxy)] at hhi
  exact ⟨by linarith, hhi⟩

/-- The same extension argument works on a compact depth interval by taking the closure
of its tested grid, including endpoints that were not themselves grid points. -/
theorem profile_bounds_on_closure {F : ℝ → ℝ} (hF : Continuous F) (K : ℝ) (S : Set ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≤ y →
      0 ≤ F y - F x ∧ F y - F x ≤ K * (y - x)) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x ≤ y →
      0 ≤ F y - F x ∧ F y - F x ≤ K * (y - x) := by
  let C := {p : ℝ × ℝ | F p.1 - F p.2 ≤ K * max (p.1 - p.2) 0}
  have hC : IsClosed C := isClosed_le
    ((hF.comp continuous_fst).sub (hF.comp continuous_snd))
    (continuous_const.mul ((continuous_fst.sub continuous_snd).max continuous_const))
  have hSC : S ×ˢ S ⊆ C := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change F x - F y ≤ K * max (x - y) 0
    by_cases hxy : x ≤ y
    · rw [max_eq_right (sub_nonpos.mpr hxy), mul_zero]
      linarith [(hS x hx y hy hxy).1]
    · rw [max_eq_left (sub_nonneg.mpr (lt_of_not_ge hxy).le)]
      exact (hS y hy x hx (lt_of_not_ge hxy).le).2
  have hcl : closure (S ×ˢ S) ⊆ C := closure_minimal hSC hC
  intro x hx y hy hxy
  have hlo := hcl (show (x, y) ∈ closure (S ×ˢ S) by rw [closure_prod_eq]; exact ⟨hx, hy⟩)
  have hhi := hcl (show (y, x) ∈ closure (S ×ˢ S) by rw [closure_prod_eq]; exact ⟨hy, hx⟩)
  change F x - F y ≤ K * max (x - y) 0 at hlo
  change F y - F x ≤ K * max (y - x) 0 at hhi
  rw [max_eq_right (sub_nonpos.mpr hxy), mul_zero] at hlo
  rw [max_eq_left (sub_nonneg.mpr hxy)] at hhi
  exact ⟨by linarith, hhi⟩

/-- Both coordinate bounds of the joint hidden/angular profile pass from a product grid
to its closed rectangle. The two Lipschitz constants are kept separately. -/
theorem joint_profile_bounds_on_closure {F : ℝ × ℝ → ℝ} (hF : Continuous F)
    (K₁ K₂ : ℝ) (A B : Set ℝ)
    (h₁ : ∀ u ∈ B, ∀ r ∈ A, ∀ s ∈ A, r ≤ s →
      0 ≤ F (s, u) - F (r, u) ∧ F (s, u) - F (r, u) ≤ K₁ * (s - r))
    (h₂ : ∀ r ∈ A, ∀ u ∈ B, ∀ v ∈ B, u ≤ v →
      0 ≤ F (r, v) - F (r, u) ∧ F (r, v) - F (r, u) ≤ K₂ * (v - u)) :
    (∀ u ∈ closure B, ∀ r ∈ closure A, ∀ s ∈ closure A, r ≤ s →
      0 ≤ F (s, u) - F (r, u) ∧ F (s, u) - F (r, u) ≤ K₁ * (s - r)) ∧
    (∀ r ∈ closure A, ∀ u ∈ closure B, ∀ v ∈ closure B, u ≤ v →
      0 ≤ F (r, v) - F (r, u) ∧ F (r, v) - F (r, u) ≤ K₂ * (v - u)) := by
  have h₁' : ∀ u ∈ B, ∀ r ∈ closure A, ∀ s ∈ closure A, r ≤ s →
      0 ≤ F (s, u) - F (r, u) ∧ F (s, u) - F (r, u) ≤ K₁ * (s - r) := by
    intro u hu
    exact profile_bounds_on_closure (hF.comp (continuous_id.prodMk continuous_const)) K₁ A (h₁ u hu)
  have h₂' : ∀ r ∈ A, ∀ u ∈ closure B, ∀ v ∈ closure B, u ≤ v →
      0 ≤ F (r, v) - F (r, u) ∧ F (r, v) - F (r, u) ≤ K₂ * (v - u) := by
    intro r hr
    exact profile_bounds_on_closure (hF.comp (continuous_const.prodMk continuous_id)) K₂ B (h₂ r hr)
  constructor
  · intro u hu r hr s hs hrs
    have hc : Continuous (fun u => F (s, u) - F (r, u)) :=
      (hF.comp (continuous_const.prodMk continuous_id)).sub
        (hF.comp (continuous_const.prodMk continuous_id))
    have hclosed : IsClosed {u | 0 ≤ F (s, u) - F (r, u) ∧
        F (s, u) - F (r, u) ≤ K₁ * (s - r)} :=
      (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
    exact closure_minimal (fun v hv => h₁' v hv r hr s hs hrs) hclosed hu
  · intro r hr u hu v hv huv
    have hc : Continuous (fun r => F (r, v) - F (r, u)) :=
      (hF.comp (continuous_id.prodMk continuous_const)).sub
        (hF.comp (continuous_id.prodMk continuous_const))
    have hclosed : IsClosed {r | 0 ≤ F (r, v) - F (r, u) ∧
        F (r, v) - F (r, u) ≤ K₂ * (v - u)} :=
      (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
    exact closure_minimal (fun s hs => h₂' s hs u hu v hv huv) hclosed hr

end Submission.Lib.K4Homogenization
