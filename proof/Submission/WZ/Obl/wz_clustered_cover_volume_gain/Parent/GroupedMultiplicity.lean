-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.GroupedMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Multiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set

namespace Interfaces

/-- A fiberwise cardinality bound times the number of active fibers bounds the
original cardinality. The bound is real-valued, so no rounding loss occurs. -/
theorem assigned_count_le {n N : ℕ} (P : Set (Fin n)) (Q : Set (Fin N))
    (f : Fin n → Fin N) {M : ℝ} (hmap : ∀ i ∈ P, f i ∈ Q)
    (hM : ∀ k ∈ Q, q {i | i ∈ P ∧ f i = k} ≤ M) : q P ≤ M * q Q := by
  classical
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := P.toFinset) (t := Q.toFinset) (g := f)
    (by simpa only [Set.mem_toFinset] using hmap) (fun _ => (1 : ℝ))
  have hcard : ∀ k, q {i | i ∈ P ∧ f i = k} =
      ∑ i ∈ P.toFinset with f i = k, (1 : ℝ) := by
    intro k
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, q, Set.ncard_eq_toFinset_card']
    congr 2
    ext i
    simp
  have hsum' : q P = ∑ k ∈ Q.toFinset, q {i | i ∈ P ∧ f i = k} := by
    simp_rw [hcard]
    rw [hsum]
    simp [q, Set.ncard_eq_toFinset_card']
  rw [hsum']
  calc
    _ ≤ ∑ _k ∈ Q.toFinset, M := Finset.sum_le_sum fun k hk => hM k (Set.mem_toFinset.mp hk)
    _ = M * q Q := by simp [q, Set.ncard_eq_toFinset_card', mul_comm]

/-- The pointwise fine, medium, and coarse cardinality bounds multiply along
two assignments of tubes to larger tubes. -/
theorem three_scale_count {n N L : ℕ} (P : Set (Fin n)) (Q : Set (Fin N))
    (R : Set (Fin L)) (f : Fin n → Fin N) (g : Fin N → Fin L)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i ∈ P, f i ∈ Q) (hg : ∀ k ∈ Q, g k ∈ R)
    (hfine : ∀ k ∈ Q, q {i | i ∈ P ∧ f i = k} ≤ A)
    (hmedium : ∀ j ∈ R, q {k | k ∈ Q ∧ g k = j} ≤ B)
    (hcoarse : q R ≤ C) : q P ≤ A * B * C := by
  have hPQ := assigned_count_le P Q f hf hfine
  have hQR := assigned_count_le Q R g hg hmedium
  calc
    _ ≤ A * q Q := hPQ
    _ ≤ A * (B * q R) := mul_le_mul_of_nonneg_left hQR hA
    _ ≤ A * (B * C) := by gcongr
    _ = _ := by ring

end Interfaces

/-- A three-scale pointwise counting estimate, with explicit power losses,
yields the multiplicity gain used by the final integration step. -/
theorem three_scale_multiplicity_bound {δ ρ θ σ ω n N Cf Cm Cc ef em ec g : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hθ : 0 < θ) (hn : 0 < n) (hN : 0 < N)
    (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    {k K L : ℕ} (Z : Fin k → Set Space) (Q : Space → Set (Fin K))
    (R : Space → Set (Fin L)) (f : Fin k → Fin K) (j : Fin K → Fin L)
    (hf : ∀ p i, p ∈ Z i → f i ∈ Q p)
    (hj : ∀ p a, a ∈ Q p → j a ∈ R p)
    (hfine : ∀ p a, a ∈ Q p →
      Interfaces.q {i | p ∈ Z i ∧ f i = a} ≤
        Cf * δ ^ (g - ef) * ((δ / ρ) ^ (-ω) * (n / N * δ * ρ / θ ^ 2) ^ σ))
    (hmedium : ∀ p b, b ∈ R p →
      Interfaces.q {a | a ∈ Q p ∧ j a = b} ≤ Cm * δ ^ (-em) * (ρ / θ) ^ (-ω - σ))
    (hcoarse : ∀ p, Interfaces.q (R p) ≤ Cc * δ ^ (-ec) * (θ ^ (-ω) * (N * θ) ^ σ)) :
    ∀ p, multiplicity Z p ≤ ENNReal.ofReal
      (Cf * Cm * Cc * δ ^ (-ω + (g - ef - em - ec)) * (n * δ) ^ σ) := by
  intro p
  have h := Interfaces.three_scale_count {i | p ∈ Z i} (Q p) (R p) f j
    (by positivity : 0 ≤ Cf * δ ^ (g - ef) * ((δ / ρ) ^ (-ω) * (n / N * δ * ρ / θ ^ 2) ^ σ))
    (by positivity : 0 ≤ Cm * δ ^ (-em) * (ρ / θ) ^ (-ω - σ))
    (hf p) (hj p) (hfine p) (hmedium p) (hcoarse p)
  have he : (Cf * δ ^ (g - ef) * ((δ / ρ) ^ (-ω) * (n / N * δ * ρ / θ ^ 2) ^ σ)) *
      (Cm * δ ^ (-em) * (ρ / θ) ^ (-ω - σ)) *
      (Cc * δ ^ (-ec) * (θ ^ (-ω) * (N * θ) ^ σ)) =
      Cf * Cm * Cc * δ ^ (-ω + (g - ef - em - ec)) * (n * δ) ^ σ := by
    calc
      _ = (Cf * Cm * Cc) * (δ ^ (g - ef) * δ ^ (-em) * δ ^ (-ec)) *
          (((δ / ρ) ^ (-ω) * (n / N * δ * ρ / θ ^ 2) ^ σ) *
            (ρ / θ) ^ (-ω - σ) * (θ ^ (-ω) * (N * θ) ^ σ)) := by ring
      _ = _ := by
        rw [three_scale_product hδ hρ hθ hn hN σ ω,
          ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        calc
          _ = (Cf * Cm * Cc) * (δ ^ (g - ef + -em + -ec) * δ ^ (-ω)) * (n * δ) ^ σ := by ring
          _ = _ := by
            rw [← Real.rpow_add hδ,
              show g - ef + -em + -ec + -ω = -ω + (g - ef - em - ec) by ring]
  rw [he] at h
  rw [multiplicity_eq_ncard, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h

/-- Combining the three counting scales and integrating gives the volume exit,
with the density and refinement losses included in the exponent budget. -/
theorem volume_gain_of_three_scale_bounds {δ ρ θ η b σ ω Cf Cm Cc ef em ec g α : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hθ : 0 < θ)
    (hCf : 0 < Cf) (hCm : 0 < Cm) (hCc : 0 < Cc)
    (hbudget : η + b + α + ef + em + ec ≤ g)
    {n N L : ℕ} (hn : 0 < n) (hL : 0 < L)
    (Y Z : Fin n → Set Space) (Q : Space → Set (Fin N))
    (R : Space → Set (Fin L)) (f : Fin n → Fin N) (j : Fin N → Fin L)
    (hZ : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (hdense : Dense δ η Y)
    (hmass : ENNReal.ofReal (δ ^ b) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i))
    (hf : ∀ p i, p ∈ Z i → f i ∈ Q p)
    (hj : ∀ p a, a ∈ Q p → j a ∈ R p)
    (hfine : ∀ p a, a ∈ Q p →
      Interfaces.q {i | p ∈ Z i ∧ f i = a} ≤
        Cf * δ ^ (g - ef) * ((δ / ρ) ^ (-ω) * ((n : ℝ) / L * δ * ρ / θ ^ 2) ^ σ))
    (hmedium : ∀ p l, l ∈ R p →
      Interfaces.q {a | a ∈ Q p ∧ j a = l} ≤ Cm * δ ^ (-em) * (ρ / θ) ^ (-ω - σ))
    (hcoarse : ∀ p, Interfaces.q (R p) ≤ Cc * δ ^ (-ec) * (θ ^ (-ω) * (L * θ) ^ σ)) :
    ENNReal.ofReal ((Cf * Cm * Cc)⁻¹ * δ ^ (ω - α) *
      (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  apply first_alternative_of_refined_multiplicity (g := g - ef - em - ec) hδ hδ1
    (mul_pos (mul_pos hCf hCm) hCc) (by linarith) hn hZ hZY hdense hmass
  exact three_scale_multiplicity_bound hδ hρ hθ (Nat.cast_pos.mpr hn)
    (Nat.cast_pos.mpr hL) hCf.le hCm.le Z Q R f j hf hj hfine hmedium hcoarse

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
