import Submission.Obl.k4_scalar_coefficient_clustering.Bins
import Submission.Obl.k4_scalar_coefficient_clustering.Input

namespace Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

theorem sum_plank_dummy_bound {D n : ℕ} (hD : 1 ≤ D) {R α β : ℝ} (hR : 1 ≤ R)
    (hα : 1 ≤ α) (hαβ : α ≤ β) (a : Fin n → Coeff) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 ≤ ω i) {c w e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (S : Finset (Fin n × Fin D))
    (hS : ∀ q ∈ S, InPlank c w e₁ e₂ (R * α / (D : ℝ)) (R * β / (D : ℝ))
      (a q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ))) :
    (∑ q ∈ S, ω q.1 / (D : ℝ)) ≤
      (18 * R * α / (D : ℝ)) * ∑ i ∈ S.image Prod.fst, ω i := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hcard : ∀ i, ((S.filter (fun q => q.1 = i)).card : ℝ) ≤ 18 * R * α := by
    intro i
    let T := S.filter (fun q => q.1 = i)
    have hinj : Set.InjOn Prod.snd (↑T : Set (Fin n × Fin D)) := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      exact Prod.ext (hx'.trans hy'.symm) hxy
    have hh := card_dummy_in_plank hD hR hα h₁ (T.image Prod.snd) (by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨q, hq, rfl⟩
      have hqi := (Finset.mem_filter.mp hq).2
      simpa only [hqi] using (hS q (Finset.mem_filter.mp hq).1).1)
    rw [Finset.card_image_of_injOn hinj] at hh
    exact hh
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image Prod.fst)
    (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩) (fun q => ω q.1 / (D : ℝ))]
  calc
    (∑ i ∈ S.image Prod.fst, ∑ q ∈ S.filter (fun q => q.1 = i), ω q.1 / (D : ℝ)) =
        ∑ i ∈ S.image Prod.fst, ((S.filter (fun q => q.1 = i)).card : ℝ) * (ω i / (D : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∑ q ∈ S.filter (fun q => q.1 = i), ω q.1 / (D : ℝ)) =
          ∑ _q ∈ S.filter (fun q => q.1 = i), ω i / (D : ℝ) from
        Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])]
      simp
    _ ≤ ∑ i ∈ S.image Prod.fst, (18 * R * α) * (ω i / (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hcard i) (div_nonneg (hω i) hDpos.le)
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_div]; ring

theorem plank_coefficient_diameter {D n : ℕ} (hD : 1 ≤ D) {R α β : ℝ} (hR : 0 ≤ R)
    (hαβ : α ≤ β) (a : Fin n → Coeff) {c w e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (S : Finset (Fin n × Fin D))
    (hS : ∀ q ∈ S, InPlank c w e₁ e₂ (R * α / (D : ℝ)) (R * β / (D : ℝ))
      (a q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ))) :
    ∀ i ∈ S.image Prod.fst, ∀ j ∈ S.image Prod.fst,
      ‖a i - a j‖ ≤ 24 * (R * β / (D : ℝ)) := by
  intro i hi j hj
  rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.mp hj with ⟨r, hr, rfl⟩
  exact coefficient_dist_in_plank h₁ h₂ ho
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ hR) (Nat.cast_nonneg D))
    (hS q hq) (hS r hr)

end
end Submission.Obl.k4_scalar_coefficient_clustering
