import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoContactGridIntegration
import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoInterceptBinCount
import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   file Submission/Obl/k4_finite_narrowness_path_improvement/FiniteJointCap.lean (namespace and imports renamed only). -/

/-! Original joint cell ceilings integrated over a contact rectangle. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

open Finset Set
open scoped Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

def baseGridCode (δ : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℤ := fun i => ⌊q i / δ⌋

theorem finite_mass_le_code_count {Ω Code : Type*} [DecidableEq Code]
    (S : Finset Ω) (P : Ω → ℝ) (code : Ω → Code) (θ : ℝ)
    (hcap : ∀ c ∈ S.image code, (∑ e ∈ S.filter (fun e => code e = c), P e) ≤ θ) :
    (∑ e ∈ S, P e) ≤ ((S.image code).card : ℝ) * θ := by
  calc
    _ = ∑ c ∈ S.image code, ∑ e ∈ S.filter (fun e => code e = c), P e :=
      (Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image.mpr ⟨e, he, rfl⟩) P).symm
    _ ≤ ∑ _c ∈ S.image code, θ := Finset.sum_le_sum hcap
    _ = _ := by simp

theorem contact_rectangle_joint_code_count {Ω : Type*}
    (S : Finset Ω) (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ)
    (T : Fin 4 → ℝ) (p : Fin 3 → ℝ) (m H A B K M δ a : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hδ : 0 < δ) (ha : 0 < a) (hδH : δ ≤ H / 2)
    (hδA : 2 * K * δ ≤ A) (hδB : 3 * K * δ ≤ B)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (hT : ∀ i : Fin 3, |T i.succ| ≤ M) (hmesh : 3 * M * δ ≤ K * a)
    (hpoint : ∀ e ∈ S, point e ∈ contactOuterBox m p H A B)
    (hfit : ∀ e ∈ S, |value e - affineBaseEval T (point e)| ≤ 2 * K * a) :
    ((S.image (fun e => (baseGridCode δ (point e), ⌊value e / a⌋))).card : ℝ) * δ ^ 3 ≤
      8192 * K * H * A * B := by
  let F := S.image (fun e => (baseGridCode δ (point e), ⌊value e / a⌋))
  let G := S.image (fun e => baseGridCode δ (point e))
  let bins : (Fin 3 → ℤ) → Finset ℤ := fun j =>
    (S.filter (fun e => baseGridCode δ (point e) = j)).image (fun e => ⌊value e / a⌋)
  have hbins (j : Fin 3 → ℤ) : ((bins j).card : ℝ) ≤ 256 * K := by
    apply hidden_intercept_bin_count_per_base_cell
      (S.filter (fun e => baseGridCode δ (point e) = j)) value point T a K M δ j
      ha hK hM hδ hT hmesh
    · intro e he
      have hc := (Finset.mem_filter.mp he).2
      intro i
      exact congrFun hc i
    · intro e he
      exact hfit e (Finset.mem_filter.mp he).1
  have hcover : F ⊆ G.biUnion (fun j => {j} ×ˢ bins j) := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨e, he, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨baseGridCode δ (point e), Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
      Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩
  have hpair : (F.card : ℝ) ≤ (G.card : ℝ) * (256 * K) := by
    calc
      _ ≤ ((G.biUnion (fun j => {j} ×ˢ bins j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
      _ ≤ ∑ j ∈ G, (({j} ×ˢ bins j).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ = ∑ j ∈ G, ((bins j).card : ℝ) := by simp
      _ ≤ ∑ _j ∈ G, 256 * K := Finset.sum_le_sum (fun j _ => hbins j)
      _ = _ := by simp
  have hbase : (G.card : ℝ) * δ ^ 3 ≤ 32 * H * A * B := by
    apply contactGrid_count_rectangle hH hA hB hK hδ hδH hδA hδB hm hv hcenter G
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨e, he, rfl⟩
    exact ⟨point e, (fun _ => rfl), hpoint e he⟩
  calc
    _ ≤ ((G.card : ℝ) * (256 * K)) * δ ^ 3 :=
      mul_le_mul_of_nonneg_right hpair (by positivity)
    _ = (256 * K) * ((G.card : ℝ) * δ ^ 3) := by ring
    _ ≤ (256 * K) * (32 * H * A * B) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by ring

/-- The original joint ceiling, with its palette factor, integrates over
the rectangle using the full hidden affine fit. Nothing is renormalized. -/
theorem finite_joint_cap_contact_rectangle {Ω Pal : Type*} [Fintype Ω] [DecidableEq Pal]
    (S : Finset Ω) (P : Ω → ℝ) (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ)
    (velocity : Ω → Pal) (z : Pal) (T : Fin 4 → ℝ) (p : Fin 3 → ℝ)
    (m H A B K M δ a C Z πz : ℝ)
    (hP : ∀ e, 0 ≤ P e) (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hπ : 0 ≤ πz)
    (hδ : 0 < δ) (ha : 0 < a) (hδH : δ ≤ H / 2)
    (hδA : 2 * K * δ ≤ A) (hδB : 3 * K * δ ≤ B)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (hT : ∀ i : Fin 3, |T i.succ| ≤ M) (hmesh : 3 * M * δ ≤ K * a)
    (hpoint : ∀ e ∈ S, point e ∈ contactOuterBox m p H A B)
    (hfit : ∀ e ∈ S, |value e - affineBaseEval T (point e)| ≤ 2 * K * a)
    (hvelocity : ∀ e ∈ S, velocity e = z)
    (hcap : ∀ (j : Fin 3 → ℤ) (n : ℤ),
      fiberMass P (fun e => ((baseGridCode δ (point e), ⌊value e / a⌋), velocity e)) ((j, n), z) ≤
        C * δ ^ 3 * Z * πz) :
    (∑ e ∈ S, P e) ≤ 8192 * C * K * H * A * B * Z * πz := by
  let code : Ω → (Fin 3 → ℤ) × ℤ := fun e => (baseGridCode δ (point e), ⌊value e / a⌋)
  have hmass := finite_mass_le_code_count S P code (C * δ ^ 3 * Z * πz) (by
    intro f _
    refine le_trans ?_ (hcap f.1 f.2)
    unfold fiberMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      have he' := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, Prod.ext he'.2 (hvelocity e he'.1)⟩
    · intro e _ _
      exact hP e)
  have hcount := contact_rectangle_joint_code_count S point value T p m H A B K M δ a
    hH hA hB hK hM hδ ha hδH hδA hδB hm hv hcenter hT hmesh hpoint hfit
  calc
    _ ≤ ((S.image code).card : ℝ) * (C * δ ^ 3 * Z * πz) := hmass
    _ = (C * Z * πz) * (((S.image code).card : ℝ) * δ ^ 3) := by ring
    _ ≤ (C * Z * πz) * (8192 * K * H * A * B) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists
