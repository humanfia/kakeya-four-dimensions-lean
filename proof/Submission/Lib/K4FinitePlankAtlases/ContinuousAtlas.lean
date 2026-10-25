import Submission.Lib.K4FinitePlankAtlases.ContinuousCover
import Submission.Lib.K4FinitePlankAtlases.PlankFrame

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/ContinuousAtlas.lean.
Uses the accepted K4ContinuousPlanks finite-approximation and weighted APIs.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Lib.K4ContinuousPlanks

private theorem recenter_plank_set {α : Type*} (b u : α → Plane)
    (S : Set α) (hS : S.Nonempty) (hbu : ∀ x ∈ S, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1)
    {c w e₁ e₂ : Plane} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (hfit : ∀ x ∈ S, InFullTracePlank (b x) (u x) c w e₁ e₂ a β) :
    ∃ c' w' : Plane, ‖c'‖ ≤ 1 ∧ ‖w'‖ ≤ 1 ∧ ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin ((plankFrame (2 * a) (2 * β) e₁ e₂)⁻¹)
        (b x + t • u x - c' - t • w')‖ ≤ 2 := by
  obtain ⟨x₀, hx₀⟩ := hS
  refine ⟨b x₀, u x₀, (hbu x₀ hx₀).1, (hbu x₀ hx₀).2, ?_⟩
  intro x hx t ht
  have heq : b x + t • u x - b x₀ - t • u x₀ =
      (b x + t • u x - c - t • w) - (b x₀ + t • u x₀ - c - t • w) := by abel
  rw [heq]
  apply plankFrame_fit (by positivity) (by positivity) h₁ h₂ ho
  · rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith [(hfit x hx t ht).1, (hfit x₀ hx₀ t ht).1])
  · rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith [(hfit x hx t ht).2, (hfit x₀ hx₀ t ht).2])

/-- A continuous original-law true atlas with geometric priority assignments.
The internal arbitrary measurable mark table incurs no assignment-format cost. -/
theorem continuous_density_atlas (H : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → Plane), Measurable b → Measurable u →
      (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ J : α → Finset (Fin D), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
    ∀ (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
    ∀ mass ρ : ℝ, 0 < mass → 0 < ρ → mass ≤ μ.real univ →
      (F.card : ℝ) ≤ mass * (D : ℝ) ^ 3 / ρ →
    ∃ m : ℕ, ∃ p : Fin m → PhysicalPlank D,
      ∃ c w : Fin m → Plane, ∃ Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ,
      (m : ℝ) ≤ (C * (D : ℝ) ^ (2 + ε) / ρ) * μ.real univ ∧
      (∀ j,
        Matrix.det (Q j) ≠ 0 ∧ ‖c j‖ + ‖w j‖ ≤ 2 ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, (|Q j e e'| + |(Q j)⁻¹ e e'|)) ≤ 32 * (D : ℝ) ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, |Q j e e'|) ≤ 16 ∧
        (∀ x ∈ firstAssignment (fun j => (p j).fitSet b u) j, ∀ t ∈ Icc (0 : ℝ) 1,
          ‖Matrix.toEuclideanLin ((Q j)⁻¹) (b x + t • u x - c j - t • w j)‖ ≤ 2) ∧
        (ρ / (C * (D : ℝ) ^ ε)) * |Matrix.det (Q j)| ≤
          μ.real (firstAssignment (fun j => (p j).fitSet b u) j)) ∧
      mass / 2 ≤ ∑ j, μ.real (firstAssignment (fun j => (p j).fitSet b u) j) := by
  obtain ⟨η, hη, C, hC, hcover⟩ := continuous_plank_cover H ε hε
  refine ⟨η, hη, 4 * C, by positivity, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong F hF mass ρ hmass hρ hm hcells
  obtain ⟨m, p, hcount, hpacket, htotal⟩ :=
    hcover D hD α μ b u hb hu hbu J hJ hlong F hF mass ρ hmass hρ hm hcells
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hd₁ : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have ha (j : Fin m) : 0 < (p j).narrow :=
    (div_pos zero_lt_one hd).trans_le (p j).narrow_ge_mesh
  have hβ (j : Fin m) : 0 < (p j).wide := (ha j).trans_le (p j).narrow_le_wide
  have ha₂ (j : Fin m) : (p j).narrow ≤ 2 := (p j).narrow_le_wide.trans (p j).wide_le_two
  have hgeometry (j : Fin m) : ∃ c w : Plane, ‖c‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧
      ∀ x ∈ firstAssignment (fun j => (p j).fitSet b u) j, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin
        ((plankFrame (2 * (p j).narrow) (2 * (p j).wide) (p j).axis₁ (p j).axis₂)⁻¹)
        (b x + t • u x - c - t • w)‖ ≤ 2 := by
    have hne : (firstAssignment (fun j => (p j).fitSet b u) j).Nonempty := by
      by_contra he
      have he' := Set.not_nonempty_iff_eq_empty.mp he
      have h := hpacket j
      rw [he', measureReal_empty] at h
      exact (not_le_of_gt (mul_pos (mul_pos (div_pos hρ (by positivity)) (ha j)) (hβ j))) h
    apply recenter_plank_set b u _ hne (fun x _ => hbu x) (ha j) (hβ j)
      (p j).unit₁ (p j).unit₂ (p j).orthogonal
    intro x hx
    exact hx.1
  choose c w hc hw hfit using hgeometry
  let Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ :=
    fun j => plankFrame (2 * (p j).narrow) (2 * (p j).wide) (p j).axis₁ (p j).axis₂
  have hdet (j : Fin m) : |Matrix.det (Q j)| = 4 * (p j).narrow * (p j).wide := by
    rw [plankFrame_abs_det (mul_pos (by norm_num) (ha j)) (mul_pos (by norm_num) (hβ j))
      (p j).unit₁ (p j).unit₂ (p j).orthogonal]
    ring
  have hinva (j : Fin m) : (2 * (p j).narrow)⁻¹ ≤ (D : ℝ) / 2 := by
    rw [← one_div]
    apply (div_le_iff₀ (mul_pos (by norm_num) (ha j))).mpr
    have h := (div_le_iff₀ hd).mp (p j).narrow_ge_mesh
    nlinarith
  have hinvβ (j : Fin m) : (2 * (p j).wide)⁻¹ ≤ (D : ℝ) / 2 := by
    rw [← one_div]
    apply (div_le_iff₀ (mul_pos (by norm_num) (hβ j))).mpr
    have h := (div_le_iff₀ hd).mp ((p j).narrow_ge_mesh.trans (p j).narrow_le_wide)
    nlinarith
  refine ⟨m, p, c, w, Q, hcount.trans ?_, ?_, htotal⟩
  · gcongr
    linarith
  · intro j
    refine ⟨abs_pos.mp (by rw [hdet]; exact mul_pos (mul_pos (by norm_num) (ha j)) (hβ j)),
      by linarith [hc j, hw j], ?_, ?_, hfit j, ?_⟩
    · apply (plankFrame_entry_budget (mul_pos (by norm_num) (ha j)) (mul_pos (by norm_num) (hβ j))
        (p j).unit₁ (p j).unit₂ (p j).orthogonal).trans
      nlinarith [ha₂ j, (p j).wide_le_two, hinva j, hinvβ j]
    · apply (plankFrame_entries (mul_pos (by norm_num) (ha j)) (mul_pos (by norm_num) (hβ j))
        (p j).unit₁ (p j).unit₂).trans
      nlinarith [ha₂ j, (p j).wide_le_two]
    · have heq : (ρ / ((4 * C) * (D : ℝ) ^ ε)) * |Matrix.det (Q j)| =
          (ρ / (C * (D : ℝ) ^ ε)) * (p j).narrow * (p j).wide := by
        rw [hdet]
        field_simp
      rw [heq]
      exact hpacket j

end Submission.Lib.K4FinitePlankAtlases
