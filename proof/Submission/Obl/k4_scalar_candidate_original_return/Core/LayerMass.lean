import Submission.Obl.k4_scalar_candidate_original_return.Core.Defs

/-!
# Mass bookkeeping for the true layers
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

/-- Disjoint priors in each world and time block: the weighted prior mass of all planks
of a layer is at most the number of time blocks. -/
theorem layer_weighted_prior_le (k : ℕ) (ℓ : Fin (a.ct k)) :
    ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
        ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i) ≤
      ((2 : ENNReal) ^ (a.ls k ℓ).T) := by
  classical
  obtain ⟨_, _, hCD, _, _⟩ := ha.layer k ℓ
  obtain ⟨_, _, hmeas, hdisj, _⟩ := hCD
  obtain ⟨_, hω0, hω1, hν, _⟩ := (ha.exact k).2.1 (a.sm k)
  set q := a.ls k ℓ with hq
  let key : Fin q.n → Fin (a.Wk k) × Fin (2 ^ q.T) := fun i => (q.world i, q.time i)
  let f : Fin q.n → ENNReal := fun i =>
    ENNReal.ofReal (ω (a.p k) (a.sm k) (q.world i)) * ν (a.p k) (a.sm k) (q.world i) (q.prior i)
  have hfib : ∀ gj : Fin (a.Wk k) × Fin (2 ^ q.T),
      ∑ i ∈ Finset.univ.filter (fun i => key i = gj), f i ≤
        ENNReal.ofReal (ω (a.p k) (a.sm k) gj.1) := by
    intro gj
    have hrw : ∀ i ∈ Finset.univ.filter (fun i => key i = gj),
        f i = ENNReal.ofReal (ω (a.p k) (a.sm k) gj.1) *
          ν (a.p k) (a.sm k) gj.1 (q.prior i) := by
      intro i hi
      have hk : key i = gj := (Finset.mem_filter.mp hi).2
      have h1 : q.world i = gj.1 := by rw [← hk]
      simp only [f, h1]
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hunion : ∑ i ∈ Finset.univ.filter (fun i => key i = gj),
        ν (a.p k) (a.sm k) gj.1 (q.prior i) =
        ν (a.p k) (a.sm k) gj.1 (⋃ i ∈ Finset.univ.filter (fun i => key i = gj), q.prior i) := by
      rw [measure_biUnion_finset]
      · intro i hi i' hi' hne
        have hk : key i = gj := (Finset.mem_filter.mp hi).2
        have hk' : key i' = gj := (Finset.mem_filter.mp hi').2
        have hw : q.world i = q.world i' := by
          have := congrArg Prod.fst (hk.trans hk'.symm)
          simpa [key] using this
        have ht : q.time i = q.time i' := by
          have := congrArg Prod.snd (hk.trans hk'.symm)
          simpa [key] using this
        exact hdisj i i' hne hw ht
      · intro i _
        exact (hmeas i).1
    rw [hunion]
    have := (hν gj.1).1
    calc ENNReal.ofReal (ω (a.p k) (a.sm k) gj.1) *
          ν (a.p k) (a.sm k) gj.1 (⋃ i ∈ Finset.univ.filter (fun i => key i = gj), q.prior i)
        ≤ ENNReal.ofReal (ω (a.p k) (a.sm k) gj.1) * 1 := by
          gcongr
          exact prob_le_one
      _ = ENNReal.ofReal (ω (a.p k) (a.sm k) gj.1) := mul_one _
  calc ∑ i, f i
      = ∑ gj : Fin (a.Wk k) × Fin (2 ^ q.T),
          ∑ i ∈ Finset.univ.filter (fun i => key i = gj), f i :=
        (Finset.sum_fiberwise Finset.univ key f).symm
    _ ≤ ∑ gj : Fin (a.Wk k) × Fin (2 ^ q.T), ENNReal.ofReal (ω (a.p k) (a.sm k) gj.1) :=
        Finset.sum_le_sum (fun gj _ => hfib gj)
    _ = ∑ g : Fin (a.Wk k), ∑ _j : Fin (2 ^ q.T), ENNReal.ofReal (ω (a.p k) (a.sm k) g) :=
        Fintype.sum_prod_type _
    _ = ∑ g : Fin (a.Wk k), (2 ^ q.T : ℕ) * ENNReal.ofReal (ω (a.p k) (a.sm k) g) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (2 ^ q.T : ℕ) * ∑ g : Fin (a.Wk k), ENNReal.ofReal (ω (a.p k) (a.sm k) g) := by
        rw [Finset.mul_sum]
    _ = (2 : ENNReal) ^ q.T := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hω0 g)]
        change (2 ^ q.T : ℕ) * ENNReal.ofReal (∑ g, ω (a.p k) (a.sm k) g) = _
        rw [hω1, ENNReal.ofReal_one, mul_one]
        push_cast
        rfl

/-- The original incidence law of each world lies, for every layer, in the union of that
layer's plank regions of the world. -/
theorem rho_compl_planks (k : ℕ) (ℓ : Fin (a.ct k)) (g : Fin (a.Wk k)) :
    a.ρ k g (⋃ (i : Fin (a.ls k ℓ).n) (_ : (a.ls k ℓ).world i = g), a.plank k ℓ i)ᶜ = 0 := by
  obtain ⟨_, _, hCD, _, hsupp⟩ := ha.layer k ℓ
  obtain ⟨_, _, _, _, hsub, _⟩ := hCD
  apply measure_mono_null _ (hsupp g)
  apply Set.compl_subset_compl.mpr
  rintro z ⟨i, hi, hz⟩
  simp only [Set.mem_iUnion]
  refine ⟨i, hi, ?_⟩
  exact ((hsub i) hz).2

/-- The prepared slack is subpower: `H ≤ N ^ ε` eventually, for every `ε > 0`. -/
theorem H_subpower (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, a.H k ≤ a.tangent k ^ ε := by
  filter_upwards [ha.scales.eventually_factor_power_le_allowance 1 1,
    ha.allowance_subpower ε hε] with k h1 h2
  have h1' : a.H k ≤ a.allowance k := by
    have h := h1
    simp only [one_mul, pow_one] at h
    exact h
  exact h1'.trans h2

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
