import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_marked_noisy_density_ceilings.Kernel

/-!
# `Submission.k4_scalar_marked_noisy_density_ceilings`

Proved from the smoothing kernel of session x0215 (o062), restated in this obligation's
namespace in `Kernel.lean`. At a point `(t, y)`, the intercept noise gives density at most
`1/σ` per marked tag; the tags that reach `(t, y)` and a hidden bin have, by their mark floors
`w j / (J · 2K)`, prior weight bounded by `J · 2K` times the original active mass in a bounded
number of original cells, which the mesh caps control. The slope noise gives the extra factor
`N^(m-u)`, and the angular caps transfer to noisy slope bins. The constant is `39360 K⁴`.
-/

namespace Submission.Obl.k4_scalar_marked_noisy_density_ceilings

open MeasureTheory Set

open MeasureTheory Set

/-- The constant of the general ceiling, with `K₁ = 2K`, `B = K` and caps `K σ² c P`. -/
theorem ceiling_const_le {K σ J L c P : ℝ} (hK : 1 ≤ K) (hσ : 0 < σ) (hJ0 : 0 ≤ (J : ℝ))
    (hJσ : J * σ ≤ 2) (hL : 0 ≤ L) (hc : 0 ≤ c) (hP : 0 ≤ P) :
    (L / σ ^ 2) * ((J * (2 * K)) * (3 * (2 * (K + 6) + 2) *
      (2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1) * (K * σ ^ 2 * c * P))) ≤
        (L / σ) * (7872 * K ^ 4 * c * P) := by
  have hceil : ((⌈4 * K⌉ : ℤ) : ℝ) ≤ 4 * K + 1 := (Int.ceil_lt_add_one _).le
  have hceil0 : (0 : ℝ) ≤ ((⌈4 * K⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.ceil_nonneg (by linarith)
  have hE : 2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1 ≤ 41 * K := by push_cast; linarith
  have hE0 : 0 ≤ 2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1 := by push_cast; linarith
  have hY : 3 * (2 * (K + 6) + 2) ≤ 48 * K := by linarith
  have hK0 : 0 ≤ K := by linarith
  have e : (L / σ ^ 2) * ((J * (2 * K)) * (3 * (2 * (K + 6) + 2) *
      (2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1) * (K * σ ^ 2 * c * P))) =
      (L / σ) * ((J * σ) * (2 * K ^ 2 * c * P) * ((3 * (2 * (K + 6) + 2)) *
        (2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1))) := by
    field_simp
  rw [e]
  have hLσ : 0 ≤ L / σ := div_nonneg hL hσ.le
  have h2 : 0 ≤ 2 * K ^ 2 * c * P := by positivity
  apply mul_le_mul_of_nonneg_left _ hLσ
  calc (J * σ) * (2 * K ^ 2 * c * P) * ((3 * (2 * (K + 6) + 2)) *
        (2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1))
      ≤ 2 * (2 * K ^ 2 * c * P) * ((48 * K) * (41 * K)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hJσ h2)
          (mul_le_mul hY hE hE0 (by positivity)) (by positivity) (by positivity)
    _ = 7872 * K ^ 4 * c * P := by ring

theorem ofReal_ceiling_le {K σ J L c P : ℝ} (hK : 1 ≤ K) (hσ : 0 < σ) (hJ0 : 0 ≤ (J : ℝ))
    (hJσ : J * σ ≤ 2) (hL : 0 ≤ L) (hc : 0 ≤ c) (hP : 0 ≤ P) :
    ENNReal.ofReal (L / σ ^ 2) * (ENNReal.ofReal (J * (2 * K)) *
      ENNReal.ofReal (3 * (2 * (K + 6) + 2) * (2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1) *
        (K * σ ^ 2 * c * P))) ≤ ENNReal.ofReal ((L / σ) * (7872 * K ^ 4 * c * P)) := by
  have hK0 : 0 ≤ K := by linarith
  have hceil0 : (0 : ℝ) ≤ ((⌈4 * K⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.ceil_nonneg (by linarith)
  have hE0 : 0 ≤ 2 * ((⌈4 * K⌉ + 15 : ℤ) : ℝ) + 1 := by push_cast; linarith
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (ceiling_const_le hK hσ hJ0 hJσ hL hc hP)


theorem rpow_neg_le_one {N x : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x) : N ^ (-x) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

theorem rpow_neg_le_rpow_neg {N x y : ℝ} (hN : 1 ≤ N) (hxy : x ≤ y) : N ^ (-y) ≤ N ^ (-x) :=
  Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Slab bound for the pure observation at hidden width `p ≥ σ`. -/
theorem pure_slab {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (b : α → Fin 5 → ℝ) {H J : ℕ} (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) {K σ δ c p P : ℝ} (hK : 1 ≤ K) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hδ : 0 ≤ δ) (hδσ : δ ≤ σ) (hc : 0 ≤ c) (hP : 0 ≤ P) (hp : σ ≤ p)
    (hJσ : 1 ≤ (J : ℝ) * σ) (hJσ2 : (J : ℝ) * σ ≤ 2)
    (htag : Measurable tag) (hb : ∀ l i, |b l i| ≤ K)
    (hround : ∀ l i, |b l i - b₀ (tag l) i| ≤ δ)
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})
    (hcap : ∀ (q : Fin 2 → ℤ) (n : ℤ), μ {r |
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = n} ≤ ENNReal.ofReal (K * σ ^ 2 * c * P))
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (n : ℤ) :
    markedLaw σ H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
        ⌊xTrace q.1.2 q.2 / p⌋ = n} ≤ ENNReal.ofReal (7872 * K ^ 4 * c * P) * volume A := by
  have hK0 : 0 ≤ K := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have h := markedLaw_ceiling_gen μ b tag b₀ w mark univ univ (L := σ) (Q := K * σ ^ 2 * c * P)
    (K₁ := 2 * K) (B := K) hσ hσ1 hδ hδσ hK0 (by linarith) hJσ hp MeasurableSet.univ
    (fun j => by rw [inter_univ, Real.volume_Icc]; exact le_of_eq (by ring_nf))
    (fun j => (measurableSet_singleton j).preimage htag) hb hround hmark
    (fun _ _ => mem_univ _) (fun q m => (measure_mono fun r hr => hr.2).trans (hcap q m)) hA n
  simp only [mem_univ, and_true] at h
  refine h.trans ?_
  gcongr
  refine (ofReal_ceiling_le hK hσ hJ0 hJσ2 hσ.le hc hP).trans (le_of_eq ?_)
  rw [div_self hσ.ne', one_mul]

/-- Slab bound with a noisy slope bin of width `ρ`: the slope noise gives `ρ/σ`. -/
theorem slope_slab {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (b : α → Fin 5 → ℝ) {H J : ℕ} (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) {K σ δ c p P ρ : ℝ} (hK : 1 ≤ K) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hδ : 0 ≤ δ) (hδσ : δ ≤ σ) (hc : 0 ≤ c) (hP : 0 ≤ P) (hp : σ ≤ p) (hρ : 0 ≤ ρ)
    (hJσ : 1 ≤ (J : ℝ) * σ) (hJσ2 : (J : ℝ) * σ ≤ 2)
    (htag : Measurable tag) (hb : ∀ l i, |b l i| ≤ K)
    (hround : ∀ l i, |b l i - b₀ (tag l) i| ≤ δ)
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})
    (hcap : ∀ (q : Fin 2 → ℤ) (n : ℤ), μ {r |
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = n} ≤ ENNReal.ofReal (K * σ ^ 2 * c * P))
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (n k : ℤ) :
    markedLaw σ H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
        ⌊xTrace q.1.2 q.2 / p⌋ = n ∧ q.1.2 1 ∈ Ico (k * ρ) ((k + 1) * ρ)} ≤
      ENNReal.ofReal ((ρ / σ) * (7872 * K ^ 4 * c * P)) * volume A := by
  have hK0 : 0 ≤ K := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have h := markedLaw_ceiling_gen μ b tag b₀ w mark (Ico (k * ρ) ((k + 1) * ρ)) univ (L := ρ)
    (Q := K * σ ^ 2 * c * P) (K₁ := 2 * K) (B := K) hσ hσ1 hδ hδσ hK0 (by linarith) hJσ hp
    measurableSet_Ico (fun j => by
      refine (measure_mono inter_subset_right).trans ?_
      rw [Real.volume_Ico]; exact le_of_eq (by ring_nf))
    (fun j => (measurableSet_singleton j).preimage htag) hb hround hmark
    (fun _ _ => mem_univ _) (fun q m => (measure_mono fun r hr => hr.2).trans (hcap q m)) hA n
  refine h.trans ?_
  gcongr
  exact ofReal_ceiling_le hK hσ hJ0 hJσ2 hρ hc hP

/-- Slab bound with a noisy slope bin of width `ρ ≥ σ` from angular cell caps. -/
theorem angular_slab {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (b : α → Fin 5 → ℝ) {H J : ℕ} (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) {K σ δ c p P ρ : ℝ} (hK : 1 ≤ K) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hδ : 0 ≤ δ) (hδσ : δ ≤ σ) (hc : 0 ≤ c) (hP : 0 ≤ P) (hp : σ ≤ p) (hρ : σ ≤ ρ)
    (hJσ : 1 ≤ (J : ℝ) * σ) (hJσ2 : (J : ℝ) * σ ≤ 2)
    (htag : Measurable tag) (hb : ∀ l i, |b l i| ≤ K)
    (hround : ∀ l i, |b l i - b₀ (tag l) i| ≤ δ)
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})
    (hcap : ∀ (q : Fin 2 → ℤ) (n k : ℤ), μ {r |
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = n ∧ ⌊b r.1 1 / ρ⌋ = k} ≤ ENNReal.ofReal (K * σ ^ 2 * c * P))
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (n k : ℤ) :
    markedLaw σ H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
        ⌊xTrace q.1.2 q.2 / p⌋ = n ∧ q.1.2 1 ∈ Ico (k * ρ) ((k + 1) * ρ)} ≤
      ENNReal.ofReal (7872 * K ^ 4 * c * (5 * P)) * volume A := by
  have hK0 : 0 ≤ K := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hρ0 : 0 < ρ := lt_of_lt_of_le hσ hρ
  set F : Set α := {l | ⌊b l 1 / ρ⌋ ∈ Finset.Icc (k - 2) (k + 2)}
  have hF : ∀ l, (Icc (b₀ (tag l) 1) (b₀ (tag l) 1 + σ) ∩ Ico (k * ρ) ((k + 1) * ρ)).Nonempty →
      l ∈ F := by
    rintro l ⟨v, ⟨hv1, hv2⟩, hv3, hv4⟩
    have hd := abs_le.mp (hround l 1)
    simp only [F, mem_ofPred_eq, Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr
      rw [le_div_iff₀ hρ0]; push_cast; nlinarith
    · have : b l 1 / ρ < ((k + 2 : ℤ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hρ0]; push_cast; nlinarith
      exact Int.lt_add_one_iff.mp (Int.floor_lt.mpr (by push_cast at this ⊢; linarith))
  have hcapF : ∀ (q : Fin 2 → ℤ) (n : ℤ), μ {r | r.1 ∈ F ∧
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = n} ≤ ENNReal.ofReal (K * σ ^ 2 * c * (5 * P)) := by
    intro q n
    calc μ {r | r.1 ∈ F ∧ (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
          ⌊xTrace (b r.1) r.2 / p⌋ = n}
        ≤ μ (⋃ k'' ∈ Finset.Icc (k - 2) (k + 2), {r |
            (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
            ⌊xTrace (b r.1) r.2 / p⌋ = n ∧ ⌊b r.1 1 / ρ⌋ = k''}) := by
          refine measure_mono ?_
          rintro r ⟨hF, h1, h2⟩
          simp only [mem_iUnion]
          exact ⟨_, hF, h1, h2, rfl⟩
      _ ≤ ∑ k'' ∈ Finset.Icc (k - 2) (k + 2), μ {r |
            (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
            ⌊xTrace (b r.1) r.2 / p⌋ = n ∧ ⌊b r.1 1 / ρ⌋ = k''} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _k'' ∈ Finset.Icc (k - 2) (k + 2), ENNReal.ofReal (K * σ ^ 2 * c * P) :=
          Finset.sum_le_sum fun k'' _ => hcap q n k''
      _ = ENNReal.ofReal (K * σ ^ 2 * c * (5 * P)) := by
          rw [Finset.sum_const, Int.card_Icc, show k + 2 + 1 - (k - 2) = 5 by ring,
            nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; norm_num; ring
  have h := markedLaw_ceiling_gen μ b tag b₀ w mark (Ico (k * ρ) ((k + 1) * ρ)) F (L := σ)
    (Q := K * σ ^ 2 * c * (5 * P)) (K₁ := 2 * K) (B := K) hσ hσ1 hδ hδσ hK0 (by linarith) hJσ hp
    measurableSet_Ico (fun j => by
      refine (measure_mono inter_subset_left).trans ?_
      rw [Real.volume_Icc]; exact le_of_eq (by ring_nf))
    (fun j => (measurableSet_singleton j).preimage htag) hb hround hmark hF hcapF hA n
  refine h.trans ?_
  gcongr
  refine (ofReal_ceiling_le hK hσ hJ0 hJσ2 hσ.le hc (by positivity)).trans (le_of_eq ?_)
  rw [div_self hσ.ne', one_mul]

end Submission.Obl.k4_scalar_marked_noisy_density_ceilings

open MeasureTheory Set Submission.Obl.k4_scalar_marked_noisy_density_ceilings in
theorem Submission.k4_scalar_marked_noisy_density_ceilings : ((fun (Noise : ∀ (σ : ℝ), MeasureTheory.Measure (Fin 5 → ℝ)) => ((fun (MarkedPrior : ∀ (σ : ℝ) (H : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ), MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) => ((fun (timeCell : ∀ (J : ℕ) (z : Fin J), Set ℝ) => ((fun (MarkedEvent : ∀ (H J : ℕ) (mark : Fin H → Fin J → Bool), Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ((fun (MarkedLaw : ∀ (σ : ℝ) (H J : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool), MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ((fun (curveX : ∀ {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ), ℝ) => ((fun (curveY : ∀ {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ), ℝ) => ((fun (meshCode : ∀ {α : Type} (b : α → (Fin 5 → ℝ)) (σ : ℝ) (p : α × ℝ), Fin 2 → ℤ) => ((fun (baseRef : MeasureTheory.Measure ((Fin 2 → ℝ) × ℤ)) => ((fun (observation : ∀ (N r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ), ((Fin 2 → ℝ) × ℤ)) => ((fun (velocityObservation : ∀ (N r u : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ), (((Fin 2 → ℝ) × ℤ) × ℤ)) => ((fun (jointRef : MeasureTheory.Measure (((Fin 2 → ℝ) × ℤ) × ℤ)) => ((fun (MeshInput : ∀ (N K d s m S U : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)) (c : ℝ) (angular : Bool), Prop) => ((fun (Coupling : ∀ (N K s m : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)) (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool), Prop) => ((fun (DensityCeilings : ∀ (N K d s m S U c : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)), Prop) => ∃ A : ℝ, 1 ≤ A ∧ ∃ q : ℕ, ∀ N K d s m S U c : ℝ, 2 ≤ N → 1 ≤ K → 0 ≤ d → d < 1 → 0 < s → s < m → 0 < S → 0 < U → U < m → 0 < c → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)) (angular : Bool), MeshInput N K d s m S U α ν μ b c angular → ∀ (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool), 1 ≤ J → 1 ≤ (J : ℝ) * N ^ (-m) → (J : ℝ) * N ^ (-m) ≤ 2 → (∀ j, 0 ≤ w j) → (∑ j, w j) = 1 → (∀ j i, |b₀ j i| ≤ K + N ^ (-10 * (m + s + 1))) → Coupling N (2 * K) s m α ν μ b H J tag b₀ w mark → DensityCeilings N (A * K ^ q) d s m S U c angular (MarkedLaw (N ^ (-m)) H J b₀ w mark)) (fun (N K d s m S U c : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : ((Fin 2 → ℝ) × ℤ) → ENNReal, Measurable g ∧ μ.map (observation N r) = baseRef.withDensity g ∧ ∀ᵐ z ∂baseRef, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧ (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) → ∃ G : (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal, Measurable G ∧ μ.map (velocityObservation N r u) = jointRef.withDensity G ∧ (∀ᵐ z ∂jointRef, G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧ (r = s → angular = true → 0 < u → u ≤ U → ∀ᵐ z ∂jointRef, G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u))))))) (fun (N K s m : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)) (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => Measurable tag ∧ (∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) ∧ (∀ l e, |b l e - b₀ (tag l) e| ≤ N ^ (-10 * (m + s + 1))) ∧ (∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})))) (fun (N K d s m S U : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)) (c : ℝ) (angular : Bool) => Measurable b ∧ MeasureTheory.IsProbabilityMeasure ν ∧ μ ≤ ENNReal.ofReal K • (ν.prod MeasureTheory.volume) ∧ μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal (K⁻¹) ≤ μ Set.univ ∧ (∀ l i, |b l i| ≤ K) ∧ (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s → μ {p | meshCode b (N ^ (-m)) p = q ∧ ⌊curveX b p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (K * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d)) ∧ (∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * (N ^ (-m)) ^ 2 ≤ K * c⁻¹ * (N ^ (-s)) ^ (-d) ∧ ∀ᵐ p ∂μ, (meshCode b (N ^ (-m)) p, ⌊curveX b p.1 p.2 / (N ^ (-s))⌋) ∈ F) ∧ (angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U → μ {p | meshCode b (N ^ (-m)) p = q ∧ ⌊curveX b p.1 p.2 / (N ^ (-s))⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (K * (N ^ (-m)) ^ 2 * c * (N ^ (-s)) ^ d * N ^ (-S * r)))))) (baseRef.prod MeasureTheory.Measure.count))) (fun (N r u : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) => (observation N r p, ⌊p.1.2 1 / (N ^ (-u))⌋)))) (fun (N r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) => (![p.2, curveY Prod.snd p.1 p.2], ⌊curveX Prod.snd p.1 p.2 / (N ^ (-r))⌋)))) (MeasureTheory.volume.prod (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))) (fun {α : Type} (b : α → (Fin 5 → ℝ)) (σ : ℝ) (p : α × ℝ) => ![⌊p.2 / σ⌋, ⌊curveY b p.1 p.2 / σ⌋]))) (fun {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ) => b l 0 + t * b l 1))) (fun {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ) => b l 2 + t * b l 3 + t ^ 2 * b l 4))) (fun (σ : ℝ) (H J : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => ((MarkedPrior σ H b₀ w).prod MeasureTheory.volume).restrict (MarkedEvent H J mark)))) (fun (H J : ℕ) (mark : Fin H → Fin J → Bool) => {p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧ p.2 ∈ timeCell J z}))) (fun (J : ℕ) (z : Fin J) => Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))))) (fun (σ : ℝ) (H : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) => ∑ j, ENNReal.ofReal (w j) • MeasureTheory.Measure.map (fun u : (Fin 5 → ℝ) => ((j : ℕ), b₀ j + u)) (Noise σ)))) (fun (σ : ℝ) => MeasureTheory.Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • MeasureTheory.volume.restrict (Set.Icc 0 σ)))) := by
  refine ⟨39360, by norm_num, 4, ?_⟩
  intro N K d s m S U c hN hK hd0 hd1 hs hsm hS hU hUm hc α _ ν μ b angular hMI H J tag b₀ w
    mark hJ1 hJσ hJσ2 hw hwsum hb₀ hCoup
  obtain ⟨hbm, hν, hμle, hμsupp, hμmass, hb, hcap, hsupp, hang⟩ := hMI
  obtain ⟨htagm, hwν, hround, hmark⟩ := hCoup
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hσ1 : N ^ (-m) ≤ 1 := rpow_neg_le_one hN1 (by linarith)
  have hδ : 0 ≤ N ^ (-10 * (m + s + 1)) := (Real.rpow_pos_of_pos hN0 _).le
  have hδσ : N ^ (-10 * (m + s + 1)) ≤ N ^ (-m) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1; nlinarith
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hfin := isFiniteMeasure_markedLaw (N ^ (-m)) H J b₀ w mark
  have hpow : ∀ r : ℝ, (N ^ (-r)) ^ d = N ^ (-d * r) := by
    intro r; rw [← Real.rpow_mul hN0.le]; ring_nf
  -- the pure slab bound at depth r
  have hpure : ∀ r : ℝ, 0 ≤ r → r ≤ s → ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ n : ℤ,
      markedLaw (N ^ (-m)) H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
        ⌊xTrace q.1.2 q.2 / N ^ (-r)⌋ = n} ≤
          ENNReal.ofReal (7872 * K ^ 4 * c * N ^ (-d * r)) * volume A := by
    intro r hr0 hrs A hA n
    rw [← hpow r]
    exact pure_slab μ b tag b₀ w mark hK hσ hσ1 hδ hδσ hc.le (by positivity)
      (rpow_neg_le_rpow_neg hN1 (by linarith)) hJσ hJσ2 htagm hb hround hmark
      (fun q n => hcap r q n hr0 hrs) hA n
  refine ⟨fun r hr0 hrs => ?_, fun r u hr0 hrs hu0 hu4 => ?_⟩
  · obtain ⟨g, hg, hmap, hle⟩ := exists_obs_density_le (markedLaw (N ^ (-m)) H J b₀ w mark)
      (N ^ (-r)) _ (hpure r hr0 hrs)
    refine ⟨g, hg, hmap, ?_⟩
    filter_upwards [hle] with z hz
    refine hz.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ K * c * N ^ (-d * r) := by positivity
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hK 4, one_le_pow₀ (n := 3) hK]
  · have hρ0 : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN0 _
    have hp : N ^ (-m) ≤ N ^ (-r) := rpow_neg_le_rpow_neg hN1 (by linarith)
    have hC1 : ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ n k : ℤ,
        markedLaw (N ^ (-m)) H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
          ⌊xTrace q.1.2 q.2 / N ^ (-r)⌋ = n ∧ q.1.2 1 ∈ Ico (k * N ^ (-u)) ((k + 1) * N ^ (-u))} ≤
            ENNReal.ofReal (39360 * K ^ 4 * c * N ^ (-d * r) * min 1 (N ^ (m - u))) *
              volume A := by
      intro A hA n k
      rcases le_or_gt u m with hum | hum
      · have hmin : min 1 (N ^ (m - u)) = 1 := min_eq_left (Real.one_le_rpow hN1 (by linarith))
        rw [hmin, mul_one]
        refine (measure_mono (Set.setOf_subset_setOf.mpr fun q hq => ⟨hq.1, hq.2.1⟩)).trans
          ((hpure r hr0 hrs A hA n).trans ?_)
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        have : 0 ≤ K * c * N ^ (-d * r) := by positivity
        nlinarith [hK4]
      · have hmin : min 1 (N ^ (m - u)) = N ^ (m - u) :=
          min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
        rw [hmin]
        have h := slope_slab μ b tag b₀ w mark (ρ := N ^ (-u)) hK hσ hσ1 hδ hδσ hc.le
          (by positivity : 0 ≤ (N ^ (-r)) ^ d) hp hρ0.le
          hJσ hJσ2 htagm hb hround hmark (fun q n => hcap r q n hr0 hrs) hA n k
        refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
        rw [hpow r, show N ^ (-u) / N ^ (-m) = N ^ (m - u) by
          rw [← Real.rpow_sub hN0]; ring_nf]
        have h1 : 0 ≤ K * c * N ^ (-d * r) * N ^ (m - u) := by positivity
        nlinarith [hK4]
    by_cases hcase : r = s ∧ angular = true ∧ 0 < u ∧ u ≤ U
    · obtain ⟨hrs', hang', hu0', huU⟩ := hcase
      have hρσ : N ^ (-m) ≤ N ^ (-u) := rpow_neg_le_rpow_neg hN1 (by linarith)
      have hC2 : ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ n k : ℤ,
          markedLaw (N ^ (-m)) H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
            ⌊xTrace q.1.2 q.2 / N ^ (-r)⌋ = n ∧
              q.1.2 1 ∈ Ico (k * N ^ (-u)) ((k + 1) * N ^ (-u))} ≤
              ENNReal.ofReal (39360 * K ^ 4 * c * N ^ (-d * s - S * u)) * volume A := by
        intro A hA n k
        have h := angular_slab μ b tag b₀ w mark (ρ := N ^ (-u))
          (P := (N ^ (-r)) ^ d * N ^ (-S * u)) hK hσ hσ1 hδ hδσ hc.le (by positivity)
          hp hρσ hJσ hJσ2 htagm hb hround hmark
          (fun q n k => by
            have := hang hang' u q n k hu0' huU
            rw [← hrs'] at this
            refine this.trans (le_of_eq ?_)
            congr 1; ring) hA n k
        refine h.trans (le_of_eq ?_)
        congr 2
        rw [hpow r, ← Real.rpow_add hN0, hrs']
        ring_nf
      have hmin2 : ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ n k : ℤ,
          markedLaw (N ^ (-m)) H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
            ⌊xTrace q.1.2 q.2 / N ^ (-r)⌋ = n ∧
              q.1.2 1 ∈ Ico (k * N ^ (-u)) ((k + 1) * N ^ (-u))} ≤
              min (ENNReal.ofReal (39360 * K ^ 4 * c * N ^ (-d * r) * min 1 (N ^ (m - u))))
                (ENNReal.ofReal (39360 * K ^ 4 * c * N ^ (-d * s - S * u))) * volume A := by
        intro A hA n k
        rcases le_total (ENNReal.ofReal (39360 * K ^ 4 * c * N ^ (-d * r) * min 1 (N ^ (m - u))))
            (ENNReal.ofReal (39360 * K ^ 4 * c * N ^ (-d * s - S * u))) with h | h
        · rw [min_eq_left h]; exact hC1 A hA n k
        · rw [min_eq_right h]; exact hC2 A hA n k
      obtain ⟨G, hG, hmap, hle⟩ := exists_obs_slope_density_le
        (markedLaw (N ^ (-m)) H J b₀ w mark) (N ^ (-r)) hρ0 _ hmin2
      refine ⟨G, hG, hmap, ?_, fun _ _ _ _ => ?_⟩
      · filter_upwards [hle] with z hz
        exact hz.trans (min_le_left _ _)
      · filter_upwards [hle] with z hz
        exact hz.trans (min_le_right _ _)
    · obtain ⟨G, hG, hmap, hle⟩ := exists_obs_slope_density_le
        (markedLaw (N ^ (-m)) H J b₀ w mark) (N ^ (-r)) hρ0 _ hC1
      refine ⟨G, hG, hmap, hle, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hcase⟩
