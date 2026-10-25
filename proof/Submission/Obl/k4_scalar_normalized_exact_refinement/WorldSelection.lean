import Submission.Obl.k4_scalar_normalized_exact_refinement.Spec
import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set Filter
open k4_scalar_linear_critical_extremizers.Split
open scoped ENNReal

noncomputable section

namespace WorldSelection

def code (p : Code) (m : ℕ → ℕ) (e : (k : ℕ) → Fin (m k) ↪ Fin (W p k))
    (c : ℕ → ℝ) : Code :=
  ⟨m, N p, K p, M p, D p, L p, d p, S p, U p,
    (fun k i => c k * ω p k (e k i)), (fun k i => ν p k (e k i)),
    (fun k i => E p k (e k i)), (fun k i => g p k (e k i)),
    (fun k i => G p k (e k i)), f p⟩

lemma sum_embedding_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (f : κ → ENNReal) : ∑ i, f (e i) ≤ ∑ j, f j := by
  classical
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

variable (p : Code) (m : ℕ → ℕ) (e : (k : ℕ) → Fin (m k) ↪ Fin (W p k)) (c : ℕ → ℝ)

lemma mass_le (hc : ∀ k, 0 ≤ c k)
    (F : (k : ℕ) → Fin (W p k) → Set (Line × ℝ)) (k : ℕ) :
    (∑ i, ENNReal.ofReal (c k * ω p k (e k i)) * mu p k (e k i) (F k (e k i))) ≤
      ENNReal.ofReal (c k) * ∑ j, ENNReal.ofReal (ω p k j) * mu p k j (F k j) := by
  simp_rw [ENNReal.ofReal_mul (hc k), mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (sum_embedding_le (e k)
    (fun j => ENNReal.ofReal (ω p k j) * mu p k j (F k j)))

theorem raw (hp : Spec.RawScalar p) (hc : ∀ k, 0 ≤ c k)
    (hsum : ∀ k, ∑ i, c k * ω p k (e k i) = 1)
    (hsuccess : ∀ k, ENNReal.ofReal ((K p k)⁻¹) ≤
      ∑ i, ENNReal.ofReal (c k * ω p k (e k i)) * mu p k (e k i) univ) :
    Spec.RawScalar (code p m e c) := by
  refine ⟨hp.1, ?_⟩
  intro k
  refine ⟨?_, (fun i => mul_nonneg (hc k) ((hp.2 k).2.1 _)), hsum k,
    (fun i => (hp.2 k).2.2.2.1 (e k i)), hsuccess k⟩
  have hcard : m k ≤ W p k := by simpa using Fintype.card_le_of_injective (e k) (e k).injective
  exact (show (m k : ℝ) ≤ W p k by exact_mod_cast hcard).trans (hp.2 k).1

/-- Pure profile typicality survives deletion of worlds and any subpower
increase of their weights. -/
theorem pure (hp : Spec.RawScalar p) (hpure : Spec.PureProfile p)
    (hc : ∀ k, 0 ≤ c k)
    (hsub : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, c k ≤ N p k ^ η) :
    Spec.PureProfile (code p m e c) := by
  refine ⟨(fun k i r hr hrL => hpure.1 k (e k i) r hr hrL), hpure.2.1, ?_⟩
  intro r τ hr hrL hτ
  obtain ⟨a, ha, htail⟩ := hpure.2.2 r τ hr hrL hτ
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [htail, hsub (a / 2) (by positivity)] with k hk hck
  have hN : 2 ≤ N p k := hp.1.1 k
  let F : (k : ℕ) → Fin (W p k) → Set (Line × ℝ) := fun k i =>
    {z | g p k i r ((![z.2, y z.1 z.2] : Fin 2 → ℝ), ⌊x z.1 z.2 / N p k ^ (-r)⌋) <
        ENNReal.ofReal (N p k ^ (-f p r - τ)) ∨
      ENNReal.ofReal (N p k ^ (-f p r + τ)) <
        g p k i r ((![z.2, y z.1 z.2] : Fin 2 → ℝ), ⌊x z.1 z.2 / N p k ^ (-r)⌋)}
  change (∑ i, ENNReal.ofReal (c k * ω p k (e k i)) * mu p k (e k i) (F k (e k i))) ≤ _
  calc
    _ ≤ ENNReal.ofReal (c k) * ∑ j, ENNReal.ofReal (ω p k j) * mu p k j (F k j) :=
      mass_le p m e c hc F k
    _ ≤ ENNReal.ofReal (N p k ^ (a / 2)) * ENNReal.ofReal (N p k ^ (-a)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hck) hk
    _ = ENNReal.ofReal (N p k ^ (-(a / 2))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_add (by linarith : 0 < N p k)]
      congr 2
      ring

end WorldSelection

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
